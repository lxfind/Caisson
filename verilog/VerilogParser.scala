package verilog;

import scala.util.parsing.combinator._

class VerilogParser extends JavaTokenParsers {
	//White space, both single-line comment and multiple-line comment will be ignored
	protected override val whiteSpace = """(\s|//.*|(?m)/\*(\*(?!/)|[^*])*\*/)+""".r
	
	def module : Parser[Module] = "module"~>ident~"("~id_list~");"~rep(block)<~"endmodule" ^^ {case name~_~args~_~blocks => new Module(name, args, blocks)}
	
	def block : Parser[Block] = decl | parameter | always | instance | assign | initial
	
	def decl : Parser[Declaration] = datatype~opt("signed")~opt(dim)~rep1sep(single_dec,",")<~";" ^^ 
	  {case dt~sign~dim~sdecl => new Declaration(dt, sign.isDefined, dim, sdecl)}
	
	def parameter : Parser[Parameter] = "parameter"~>ident~"="~expr<~";" ^^ {case name~_~value => new Parameter(name, value)}
	
	def initial : Parser[Initial] = "initial"~>stmts ^^ {case s => new Initial(s)}
	
	def always : Parser[Always] = "always @("~>alwaysType~")"~stmts ^^ {case at~_~stmts => Always(at, stmts)}
	
	def instance : Parser[Instance] = ident~ident~"("~rep1sep(wiring,",")<~");" ^^ {case mName~iName~_~args => new Instance(mName, iName, args)}
	
	def assign : Parser[Assign] = "assign"~>lvalue(true)~"="~expr<~";" ^^ {case id~_~e => new Assign(id,e)}
	
	def wiring : Parser[(String,Expression)] = "."~>ident~"("~expr<~")" ^^ {case name~_~e => (name,e)}
	
	def alwaysType : Parser[AlwaysType] = ("*" ^^^ (Star)
										| "posedge clk or posedge reset" ^^^ (Clk))
	
	def datatype : Parser[DataType] = ("input" ^^^ (Input)
									| "output" ^^^ (Output)									
									| "wire" ^^^ (Wire)
									| "reg" ^^^ (Register)
									| "integer" ^^^ (Integer))								
	
	def single_dec : Parser[SingleDec] = ident~opt(dim) ^^ { case id~dim => new SingleDec(id, dim)} 
	
	def dim : Parser[Dim] = "["~>expr~opt(":"~>expr)<~"]" ^^ {case l~None => SingleDim(l)
															  case l~Some(h) => DoubleDim(l,h)}
	
	def id_list : Parser[List[String]] = repsep(ident, ",")
	
	def stmts : Parser[StatementList] = ("begin"~>rep(stmt)<~"end" ^^ {case s => new StatementList(s)})									
	
	def stmtOrstmts : Parser[StatementList] = (stmts
											| stmt ^^ {case s => new StatementList(List(s))})
	
	def stmt : Parser[Statement] = nonblockAssign | conditional | cases | forLoop | debug
	
	def nonblockAssign : Parser[NonBlockAssign] = lvalue(false)~"<="~expr<~";" ^^ {case l~_~e => new NonBlockAssign(l,e)}
	
	def conditional : Parser[Conditional] = "if"~"("~>expr~")"~stmtOrstmts~opt("else"~>stmtOrstmts) ^^ {case cond~_~ifs~elses => new Conditional(cond, ifs, elses)}
	
	def cases : Parser[Case] = "case"~"("~>expr~")"~rep1(caseElement)<~"endcase" ^^ {case cond~_~body => new Case(cond, body)}
	
	def caseElement : Parser[(String,StatementList)] = (rep1sep((verilogNumber | ident),","))~":"~stmtOrstmts ^^ {case value~_~s => (value.mkString(","),s)}
	
	def forLoop : Parser[ForLoop] = "for"~"("~>ident~"="~expr~";"~expr~";"~ident~"="~expr~")"~stmts ^^ {case id~_~init~_~cond~_~_~_~step~_~s => new ForLoop(id, init, cond, step, s)}
	
	def debug : Parser[Debug] = """\$.+""".r ^^ (Debug)
	
	def expr : Parser[Expression] = ternaryExpr
	
	def ternaryExpr : Parser[Expression] = binaryExpr~opt("?"~>ternaryExpr~":"~ternaryExpr) ^^ {	
      case cond~Some(ifb~_~elseb) => TernaryExpression(cond, ifb, elseb) 
      case cond~None => cond} 
	
	def binaryExpr: Parser[Expression] = unaryExpr~rep(binop~unaryExpr) ^^ {
      case left~lt => lt.length match {
        case 0 => left 
        case _ => lt.foldLeft(left)((left,right) => right match { 
          case op~rt => new BinaryExpression(left,rt,op)})}
    }
	
	def unaryExpr: Parser[Expression] = ( parenExpr
    								| unop~unaryExpr ^^ { case op~e => UnaryExpression(e, op) } )
    
    def parenExpr: Parser[Expression] = ( singulars
    								| "("~>expr<~")" ^^ { case e => ParenExpression(e)})
    								
      
    def concatExpr: Parser[Expression] = "{"~rep1sep(expr, ",")~"}" ^^ { case "{"~exprs~"}" =>
      ConcatExpression(exprs)
    }       

    def singulars: Parser[Expression] = ( verilogNumber ^^ (Number)
                                  | lvalue(true)
                                  | concatExpr)
    
    def arrayIndexing: Parser[Expression] = ("["~>expr<~"]"
    									| "["~>expr~":"~expr<~"]" ^^ {case e1~op~e2 => new BinaryExpression(e1,e2,op)})
    
    def binop: Parser[String] = "+" | "-" | "&&" | "||" | "<<<" | ">>>" | "<<" | ">>" | "*" | "/" | "&" | "|" | "==" | "<=" | ">=" | "<" | ">" | "!=" | "^"                                
    
    def unop: Parser[String] = "!" | "~" | "&" | "|"
    
    def verilogNumber: Parser[String] = (binaryNumber | hexNumber | decNumber | decimalNumber)
    
    def binaryNumber: Parser[String] = """\d*\'b[01ZXx?]+""".r
    
    def hexNumber: Parser[String] = """\d*\'h[0-9a-fA-FX]+""".r
    
    def decNumber: Parser[String] = """\d*\'d[0-9]+""".r   

    def lvalue(isRead : Boolean): Parser[Lvalue] = ( ident~arrayIndexing~opt(arrayIndexing) ^^ { 	case a~e1~None => ArrayExpression(a, e1, isRead) 
    																				case a~e1~Some(e2) => VectorExpression(a, e1, e2, isRead)}
                               | ident ^^ {case a => Variable(a,isRead)})
	  
}