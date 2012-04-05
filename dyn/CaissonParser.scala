/*
  Please refer to licensing information in LICENSE.txt
  Author: Vineeth Kashyap
  Email: vineeth@cs.ucsb.edu
  In this file, the parser-combinator for Caisson is specified.
*/
package dyn

import scala.util.parsing.combinator._

class DynamicCaissonParser extends RegexParsers {
    protected override val whiteSpace = """(\s|//.*|(?m)/\*(\*(?!/)|[^*])*\*/)+""".r

    def prog: Parser[Program] = "prog"~>ident~"("~repsep(ident, ",")~")"~"="~declarations~"in"~definition ^^ {case name~"("~params~")"~"="~decl~"in"~defn => 
                                                                                                                new Program(name, params, decl, defn)}
    
    def declarations: Parser[List[DataDeclaration]] = rep1(dataDeclaration<~";") ^^ ((lst: List[List[DataDeclaration]]) => 
                                                                                       lst.reduceLeft((a: List[DataDeclaration], b: List[DataDeclaration]) => a ++ b))
    
    def dataDeclaration: Parser[List[DataDeclaration]] = dataStructure~rep1sep(pair, ",") ^^ { case ds~lst => lst.map((x => new DataDeclaration(new DataStructure(ds, x._3), x._1, x._2))) }
    
    def pair: Parser[(String, SecurityLevel, Option[(Int, Int)])] = ident~opt(dataSize)~opt(":"~ident) ^^ { case a~ds~b => (a, b match {
      case Some(":"~l) => Fixed(ConcreteTag(l))
      case None => Dynamic(ConcreteTag("L"))  //by default, if no tag is mentioned, make it low. It can be changed later via setLevel
    }, ds) }
    
    def dataStructure: Parser[DataStructure] = dataType~opt(dataSize) ^^ { case dt~ds => new DataStructure(dt, ds, None) }
    
    def dataType: Parser[DataType] = ( "input" ^^ (_ => Input()) 
                                     | "output" ^^ (_ => Output()) 
                                     | "regstar" ^^ (_ => RegStar())
                                     | "regposclk" ^^ (_ => RegPosClk())
                                     | "regnegclk" ^^ (_ => RegNegClk())
                                     | "inout" ^^ (_ => Inout())
                                     | "imem" ^^ (_ => Imem())
                                     | "dmem" ^^ (_ => Dmem())
                                     | "wire" ^^ (_ => Wire()) )
    
    def dataSize: Parser[(Int, Int)] = "["~>wholeNumber~":"~wholeNumber<~"]" ^^ { case a~":"~b => (a.toInt, b.toInt) }
    
    def definition: Parser[Definition] = ("let"~>rep1(stateDefinition)~"in"~command ^^ { case sdList~"in"~cmd => LetDefinition(sdList, cmd) }
                                  | command)
    
    def stateDefinition: Parser[StateDefinition] = "state"~>pair~"="~"{"~definition<~"}" ^^ {
      case p~"="~"{"~defs => new StateDefinition(p._1, p._2, defs)
    }

    // :\ stands for foldRight
    def varTypedList: Parser[List[Tuple2[String, String]]] = repsep(ident~":"~ident,",") ^^ (lst => (lst :\ List[Tuple2[String, String]]())((e, l) => e match {case a~":"~b => (a,b) :: l}))
    
    def constraintList: Parser[List[Tuple2[String,String]]] = "["~>repsep(ident~"<"~ident,",")<~"]" ^^ (lst => lst.map((x => x match { case a~"<"~b => (a,b) })))
    
    def command: Parser[Command] = rep1(statement) ^^ (Command)
    
    def statement: Parser[Statement] = assignment | branch | jump | fall | "skip"~";" ^^ (_ => Skip()) | kase | setTag
    
    def assignment: Parser[Assignment] = lvalue~":="~expr~otherwise ^^ { case lv~":="~rv~owise => Assignment(lv, rv, owise) }

    def setTag: Parser[Statement] = setArrayRegTag | setRegTag | setStateTag //TODO: can we define a more precise type than just Statement here?

    def setStateTag: Parser[SetStateTag] = "SetStateTagOf"~>"("~ident~","~tag~")"~otherwise ^^ {
      case "("~st~","~tg~")"~owise => SetStateTag(st, tg, owise)
    }

    def setRegTag: Parser[SetRegisterTag] = "SetRegisterTagOf"~>"("~ident~","~tag~")"~otherwise ^^ {
      case "("~rg~","~tg~")"~owise => SetRegisterTag(rg, tg, owise)
    }

    def setArrayRegTag: Parser[SetArrayRegisterTag] = "SetRegisterTagOf"~>"("~arrayExpression~","~tag~")"~otherwise ^^ {
      case "("~ae~","~tg~")"~owise => SetArrayRegisterTag(ae, tg, owise)
    }

    def arrayExpression: Parser[ArrayExpr] = ident~arrayIndexing~opt(arrayIndexing) ^^ { case a~e1~e2 => ArrayExpr(Variable(a), e1, e2) }

    def tag: Parser[Tag] = ( "PC" ^^ (_ => PC())
                           | arrayExpression<~".tag" ^^ (RegisterArrayReferenceTag)
                           | ident<~".tag" ^^ (StateOrRegisterReferenceTag)
                           | ident ^^ (ConcreteTag) )

    def expr: Parser[Expr] = ( arithExpr~condOp~arithExpr ^^ { case left~op~right => ComplexExpr(left, right, op) }
                                | "("~>arithExpr~condOp~arithExpr<~")" ^^ { case left~op~right => ComplexExpr(left, right, op) }
                                | arithExpr
                                | unop~expr ^^ { case op~e => UnaryExpr(op, e) } )
        
    def arithExpr: Parser[Expr] = term~rep(binop~term)  ^^ { case t~lt => lt.foldLeft(t)((left, right) => right match { case op~rt => ComplexExpr(left, rt, op) }) }
   
    
    def term: Parser[Expr] = ( verilogNumber ^^ (Number) 
                            | arrayExpression
                            | concatExpr
                            | ident               ^^ (Variable)
                            | unop~arithExpr ^^ { case op~e => UnaryExpr(op, e) }                            
                            | "("~>arithExpr<~")" )      

    def concatExpr: Parser[Expr] = "{"~rep1sep(singulars, ",")~"}" ^^ { case "{"~singularList~"}" =>
      SingularCollection(singularList)
    }

    def singulars: Parser[Expr] = ( verilogNumber       ^^ (Number)
                                  | ident~arrayIndexing ^^ { case a~e => ArrayExpr(Variable(a), e, None) }
                                  | ident               ^^ (Variable) )

    def arrayIndexing: Parser[Expr] = "["~>expr<~"]"
    
    def binop: Parser[String] = "+" | "-" | "&&" | "||" | "<<" | ">>" | "*" | "/" | ":" | "&" | "|"
                                
    def condOp: Parser[String] = "==" | "<" | ">" | "<=" | ">=" | "!="
    
    def unop: Parser[String] = "!" | "~"
                                        
    def branch: Parser[Branch] = "if"~>expr~"then"~"{"~command~"}"~opt("else"~"{"~command~"}") ^^ { case cond~"then"~"{"~tbody~"}"~Some("else"~"{"~ebody~"}") => 
                                                                                                                                        Branch(cond, tbody, Some(ebody))
                                                                                                    case cond~"then"~"{"~tbody~"}"~None => Branch(cond, tbody, None) }
    
    def kase: Parser[Kase] = caseHeader~"{"~rep1(caseBody)<~"}" ^^ { case cond~"{"~cList => Kase(cond, cList.reduceLeft((a, b) => a ++ b)) }
    
    def caseBody: Parser[Map[List[String], Command]] = caseList~":"~"{"~command<~"}" ^^ { case key~":"~"{"~c => Map(key -> c) }
    
    def caseHeader: Parser[Expr] = "case"~"("~expr<~")" ^^ { case "case"~"("~e => e }
    
    def caseList: Parser[List[String]] = ( rep1sep(verilogNumber, ",") 
                                         | "default" ^^ (_ => List("default")) )
    
    def jump: Parser[Jump] =  "goto"~>ident~otherwise ^^ { case target~owise => Jump(target, owise) }

    def fall: Parser[Fall] = "fall"~>otherwise ^^ { case owise => Fall(owise) }

    def otherwise: Parser[Option[Command]] = ( "otherwise"~>"{"~command<~"}" ^^ { case "{"~c => Some(c) }
                                             | ";" ^^ (_ => None) )

    def verilogNumber: Parser[String] = (binaryNumber | floatingPointNumber)

    def lvalue: Parser[Expr] = ( ident~arrayIndexing~opt(arrayIndexing) ^^ { case a~e1~e2 => ArrayExpr(Variable(a), e1, e2) }
                               | ident ^^ (Variable) )

    def ident: Parser[String] = """[a-zA-Z_]\w*""".r ^^ { case "PC" => throw new CaissonParseException("Cannot use PC as an indentifier, it is reserved")
                                                          case x => x }
    
    def wholeNumber: Parser[String] = """-?\d+""".r
    
    def decimalNumber: Parser[String] = """(\d+(\.\d*)?|\d*\.\d+)""".r

    def stringLiteral: Parser[String] = ("\""+"""([^"\p{Cntrl}\\]|\\[\\/bfnrt]|\\u[a-fA-F0-9]{4})*"""+"\"").r
    
    def floatingPointNumber: Parser[String] = """-?(\d+(\.\d*)?|\d*\.\d+)([eE][+-]?\d+)?[fFdD]?""".r
    
    def binaryNumber: Parser[String] = """\d+\'b[01]+""".r
}

class CaissonParseException(msg: String) extends Exception {
  def message: String = msg
}

// For testing
//import java.io.FileReader

object ParserTester {
  def main(args: Array[String]) {
//        if (args.length != 1) {
//          println("Please provide caisson filename to be compiled")
//          exit(-1)
//        }
//        val reader = new FileReader(args(0))
    val parser = new DynamicCaissonParser()
    //parser tests
    println(parser.parseAll(parser.setTag, "SetStateTagOf(S1, PC) otherwise { local_timer := 0; }"))
    println(parser.parseAll(parser.setTag, "SetRegisterTagOf(reg1, S1.tag);"))
    println(parser.parseAll(parser.setTag, "SetRegisterTagOf(regarr[b][20], regarr[a][20].tag);"))
  }


}
