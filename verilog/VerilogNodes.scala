package verilog;

sealed abstract class VerilogASTNode {
	
	def codeGen(env : Environment) : String  
	  
	protected def wrapTab(str : String) : String = str.split(newline).map("\t"+_+"\n").mkString
	
	protected def wrapDim(dim : Option[Dim], env : Environment) = dim match {
	  case None => ""
	  case Some(d) => d.codeGen(env)
	}
	
	protected def removeUntagged(sigs : List[String]) = sigs.remove(isUntagged(_)) 
	protected def tagHelp[T](id : String, fif : T, felse : T) = (if (isUntagged(id)) fif else felse)		
	protected def rename(id : String, suffix : String) = tagHelp[String](id, id, id+suffix)
	protected def isUntagged(id : String) = unTagged.contains(id)
		
	protected val newline = "\n"  
	protected val sectypes = List(("H","_h"),("L","_l"))
	protected val unTagged = List("clk", "reset", "mode")
	protected val unTaggedType = "L"
}

/* Module */
class Module(val name : String, args : List[String], blocks : List[Block]) extends VerilogASTNode {

  def symbols = get[Declaration].flatMap(x => x.decs.map(y => (y.id->x.datatype))).toMap
  
  def codeGen(env : Environment) : String = (if (env.isStatic) staticCode(env) else dynamicCode(env))
  
  def semCheck(fileName : String) = {
    // Module name must be identical to filename excluding extension
    if (!fileName.equals(name)) throw new Exception("File name should be identical to module name: "+fileName + " vs. "+name)
    blocks.foreach(_.semCheck(args))
  }
  
  private def staticCode(env : Environment) : String = {    
    "prog " + name + "(" + dupArg.mkString(",") + ") =" + newline + 
    wrapTab(getCode[Declaration](env)) + (if (env.isMain) "wire exp:L;" + newline else "") + 
    wrapTab(getCode[Parameter](env)) +
    "in" + newline + 
    "let state master:L() = {" + newline +
    wrapTab(//master code +
        ((if (env.isMain) "mode <= 0;" else "") + newline) + 
        "goto group(" + allSignals(sectypes(1)._2) +");") + newline +
    "}" + newline + newline +
    "state lease:L() = {" + newline +
    wrapTab(//lease code +
        ((if (env.isMain) "mode <= 1;" else "") + newline) +
        "goto group(" + allSignals(sectypes(0)._2) +");") + newline +
    "}" + newline + newline + 
    "state group:L(" + allSignals(":T") + ")[L<T,T<H] = {" + newline + 
    wrapTab("let state pipeline:T() = {" + newline +
        wrapTab(getCode[Always](env)) +
        "goto pipeline();" + newline +
        "}" + newline +
        "in" + newline +
        (if (env.isMain)
        (wrapTab("if (exp) begin" + newline +        
		wrapTab("goto master();") +
		"end else if (!mode && timer_l>0) begin" + newline +
		wrapTab("goto lease();") +
		"end else begin" + newline +		
		wrapTab("if (mode) begin" + newline +
		    wrapTab("timer_l <= timer_l - 1;") +
			"end" + newline +
			"fall;") +
		"end")) else wrapTab("fall;"))) +
    "}" + newline +
    "in" + newline +
    wrapTab("fall;") +
    //reset code? +
    newline +
    (if (env.isMain) "assign exp = mode && timer_l==0;" + newline else "") +
    getCode[Assign](env) + newline + newline +
    getCode[Instance](env) + newline +
    "reset {" + newline + Store.init.stmts.flatMap(_ match {
      case x : NonBlockAssign => sectypes.map(s => x.lhand.codeGen(s._2) + " <= " + x.rhand.codeGen(s._2) + ";" + newline)
      case t => println("non-assign statment in reset code discarded: "+t); List()
    }).mkString + "}"	// For reset code
  }
  
  def p[T](task : Task[T]):T = blocks.foldLeft(task.emptyValue)((a,b) => task.mergeFunction(a,b.p(task)))
  
  private def dynamicCode(env : Environment) : String = {
    "prog " + name + "(" + dupArg.mkString(",") + ") =" + newline + 
    wrapTab(getCode[Declaration](env)) + (if (env.isMain) "wire exp:L;" + newline else "") + 
    wrapTab(getCode[Parameter](env)) +
    "in" + newline + 
    "let state master:L() = {" + newline +
    wrapTab(//master code +
        ((if (env.isMain) "mode <= 0;" else "") + newline) + 
        "goto group(" + allSignals(sectypes(1)._2) +");") + newline +
    "}" + newline + newline +
    "state lease:L() = {" + newline +
    wrapTab(//lease code +
        ((if (env.isMain) "mode <= 1;" else "") + newline) +
        "goto group(" + allSignals(sectypes(0)._2) +");") + newline +
    "}" + newline + newline + 
    "state group:L(" + allSignals(":T") + ")[L<T,T<H] = {" + newline + 
    wrapTab("let state pipeline:T() = {" + newline +
        wrapTab(getCode[Always](env)) +
        "goto pipeline();" + newline +
        "}" + newline +
        "in" + newline +
        (if (env.isMain)
        (wrapTab("if (exp) begin" + newline +        
		wrapTab("goto master();") +
		"end else if (!mode && timer_l>0) begin" + newline +
		wrapTab("goto lease();") +
		"end else begin" + newline +		
		wrapTab("if (mode) begin" + newline +
		    wrapTab("timer_l <= timer_l - 1;") +
			"end" + newline +
			"fall;") +
		"end")) else wrapTab("fall;"))) +
    "}" + newline +
    "in" + newline +
    wrapTab("fall;") +
    //reset code? +
    newline +
    (if (env.isMain) "assign exp = mode && timer_l==0;" + newline else "") +
    getCode[Assign](env) + newline + newline +
    getCode[Instance](env) + newline +
    "reset {" + newline + Store.init.stmts.flatMap(_ match {
      case x : NonBlockAssign => sectypes.map(s => x.lhand.codeGen(s._2) + " <= " + x.rhand.codeGen(s._2) + ";" + newline)
      case t => println("non-assign statment in reset code discarded: "+t); List()
    }).mkString + "}"	// For reset code
  }
  
  private def dupArg = { 
    args.foldLeft(List[String]())((a:List[String], b:String) => 
      a++tagHelp(b, List(b), sectypes.map(b+_._2)))
  }
  
  private def addSuffix(args : List[String], suffix : String) : List[String] = removeUntagged(args).map(_+suffix)
   
  private def get[T](implicit m: Manifest[T]) = blocks.filter(Manifest.singleType(_) <:< m).map(_.asInstanceOf[T])
  
  private def getCode[T<:VerilogASTNode](env : Environment)(implicit m: Manifest[T]) : String = 
    get[T].foldLeft("")((a:String,b:T) => a+b.codeGen(env)) 
  
  private def allSignals(suffix : String) = 
    addSuffix(get[Declaration].foldLeft(List[String]())((a:List[String],b:Declaration) => a++b.getSignals), suffix).mkString(",")
  
  // Add register mode and timer to the declaration
  def patch(env : Environment) = {
    val extra_decs = (if (env.isMain) List(Declaration(Register, false, None, List(SingleDec("mode", None))))
    					else List()) 
    val all_output = get[Declaration].foldLeft(List[String]())((a:List[String],b:Declaration) => a++(if (b.getdatatype.equals(Output)) b.getSignals else List()))
    val decs_remove_dup = get[Declaration].map(_.removeDup(all_output)).remove(_.isEmpty)
    val decs_remove_integer = decs_remove_dup.remove(_.getdatatype.equals(Integer))
    val decs_regwires = decs_remove_integer.filter(_.datatype.equals(Register)).map(x => new Declaration(Wire, x.isSigned, x.dim, x.decs.remove(y => env.clkAssignSet.contains(y.id)))).remove(_.decs.isEmpty)
    val decs_remove_regwires = decs_remove_integer.map(x => if (x.datatype.equals(Register)) new Declaration(x.datatype, x.isSigned, x.dim, x.decs.filter(y => env.clkAssignSet.contains(y.id))) else x).remove(_.decs.isEmpty)
    updateVectors
    Store.params = this.get[Parameter].map(_.name)
    new Module(name, args, blocks.remove(_.isInstanceOf[Declaration]) ++ decs_remove_regwires ++ extra_decs ++ decs_regwires)
  }
  
  private def updateVectors {
    Store.vectors = Map()
    get[Declaration].filter(_.dim.isDefined).map(x => x.decs.filter(_.dim.isDefined).map(y => (y.id,x.dim.get.asInstanceOf[DoubleDim].range1.asInstanceOf[Number].value.toInt))).flatten.foreach(x => {
      Store.vectors = Store.vectors ++ Map(x._1 -> x._2)
    })
  }    
}

/* High level blocks */
sealed abstract class Block extends VerilogASTNode {
  def semCheck(moduleArgs : List[String]) {}
  def p[T](task : Task[T]):T = task.emptyValue
}

case class Assign(lhand : Expression, rhand : Expression) extends Block {
  def codeGen(env : Environment) = sectypes.map(s => "assign " + lhand.codeGen(s._2) + " = " + rhand.codeGen(s._2) + ";" + newline).mkString   
}

object Always {
  def apply(alwaysType : AlwaysType, stmts : StatementList) = {    
    alwaysType match {
      case Star => new Always(Star, stmts)
      case Clk => new Always(Clk, (if (stmts.stmts.size==1) stmts.stmts.first match {
        case c : Conditional => c.cond match {
          case v : Variable => if (v.id.equals("reset")) {
        	  Store.init = c.ifstmts;            	  
        	  if (c.elsestmts.isEmpty) new StatementList(List()) else c.elsestmts.get} 
          	else stmts
          case _ => stmts
        }
        case _ => stmts
      } else stmts))
    }
  }
}

class Always(alwaysType : AlwaysType, stmts : StatementList) extends Block {        
  def codeGen(env : Environment) = stmts.codeGen(env)
  override def semCheck(moduleArgs : List[String]) { 
    stmts.semCheck(moduleArgs, alwaysType.equals(Clk))
  }
  
  override def p[T](task : Task[T]):T = task match {
    case GetAssignVarSet => alwaysType match {
      case Clk => stmts.p(task)
      case _ => task.emptyValue
    }
    case _ => task.emptyValue
  }
}

case class Instance(moduleName : String, instName : String, args : List[(String,Expression)]) extends Block {
  def codeGen(env : Environment) = (if (env.allModuleNames.contains(moduleName)) (if (env.isStatic) staticCode else dynamicCode) 
      else {println("Instantiation "+moduleName+" discarded since it is not implemented."); ""})
  
  def staticCode = {
    moduleName + " " + instName + "(" +
    args.foldLeft(List[(String,String)]())((a:List[(String,String)], b:(String,Expression)) => 
      a++tagHelp(b._1, List((b._1,b._1)), (sectypes.map((s:(String,String)) => 
        (b._1+s._2, b._2.codeGen(s._2)))))).map((a:(String,String)) => 
          "."+a._1+"("+a._2+")").mkString(",") +
    ");" + newline
  }
  
  def dynamicCode = ""
}

case class Initial(stmts : StatementList) extends Block {
  def codeGen(env : Environment) = {
    println("Warning: initialization discarded");
    ""
  }
}

/* Parameters */
case class Parameter(name : String, value : Expression) extends Block {
  def codeGen(env : Environment) = "parameter " + name + " = " + value.codeGen("") + ";" + newline
}

/* Declarations */
case class Declaration(datatype : DataType, isSigned : Boolean, dim : Option[Dim], decs : List[SingleDec])  extends Block {
  def getdatatype = datatype
  
  def codeGen(env : Environment) = {
    (datatype match {
		case Wire => "wire"
  		case Register => "reg"
  		case Input => "input"
  		case Output => "output"  		
  		case Integer => "integer"
  	}) + 
  	(if (isSigned) " signed" else "") +
  	(dim match {
  		case None => ""
  		case Some(d) => d.codeGen(env)
  	}) + " " +
  	(if (env.isStatic) staticCode(env) else dynamicCode) +
  	";" + newline
  }
  
  def staticCode(env : Environment) = decs.map(_.codeGen(env)).mkString(",")
    
  def dynamicCode = ""
  
  def getSignals = decs.map(_.getid)
  
  def removeDup(all_output : List[String]) = (if (datatype.equals(Register)) Declaration(datatype, isSigned, dim, decs.remove((s:SingleDec) => all_output.contains(s.getid))) else this)
  
  def isEmpty = decs.isEmpty
}

case class SingleDec(id : String, dim : Option[Dim]) extends VerilogASTNode {
  def getid = id
  
  def codeGen(env : Environment) = 
    tagHelp(id, id+":"+unTaggedType+wrapDim(dim, env),  
        sectypes.map((s:(String,String)) => id + s._2 + wrapDim(dim, env) + ":" + s._1).mkString(","))
       
}

/* Dimension */
sealed abstract class Dim extends VerilogASTNode

case class SingleDim(size : Expression) extends Dim {
  def codeGen(env : Environment) = "[" + size.codeGen(env) + "]"
}

case class DoubleDim(range1 : Expression, range2 : Expression) extends Dim {
  def codeGen(env : Environment) = "[" + range1.codeGen(env) + ":" + range2.codeGen(env) + "]"
}


/* Data types */
sealed trait DataType
case object Wire extends DataType
case object Register extends DataType
case object Input extends DataType
case object Output extends DataType
case object Integer extends DataType


/* Always block type */
sealed trait AlwaysType
case object Star extends AlwaysType
case object Clk extends AlwaysType


/* Statements */
sealed abstract class Statement extends VerilogASTNode {
  def semCheck(moduleArgs : List[String], isAlwaysClk : Boolean) {}
  def p[T](task : Task[T]):T = task.emptyValue
}

case class Conditional(cond : Expression, ifstmts : StatementList, elsestmts : Option[StatementList]) extends Statement {
  def codeGen(env : Environment) = {
    "if (" + cond.codeGen(env) + ") begin" + newline +
    wrapTab(ifstmts.codeGen(env)) +
    "end" + (elsestmts match {
      case None => ""
      case Some(s) => " else begin" + newline + wrapTab(s.codeGen(env)) + "end"
    }) + newline 
  }
  
  override def semCheck(moduleArgs : List[String], isAlwaysClk : Boolean) {
    ifstmts.semCheck(moduleArgs, isAlwaysClk)
    (if (!elsestmts.isEmpty) elsestmts.get.semCheck(moduleArgs, isAlwaysClk))
  }
  
  override def p[T](task : Task[T]):T = task match {
    case GetAssignVarSet => task.mergeFunction(ifstmts.p(task), (if (elsestmts.isDefined) elsestmts.get.p(task) else task.emptyValue))
  }
}

case class NonBlockAssign(lhand : Lvalue, rhand : Expression) extends Statement {
  def codeGen(env : Environment) = lhand.codeGen(env) + " <= " + rhand.codeGen(env) + ";"
  
  // Check that output should not be assigned under always(clk) blocks
  override def semCheck(moduleArgs : List[String], isAlwaysClk : Boolean) {
    (if (isAlwaysClk) {
      val lName = lhand match {
      	case v:Variable => v.getname
      	case v:ArrayExpression => v.getname
      	case v:VectorExpression => v.getname
      	case _ => throw new Exception("Left hand side of non blocking assigns can only be either Variable, ArrayExpression or VectorExpression: "+this.codeGen(null))
      }
      (if (moduleArgs.contains(lName)) throw new Exception("Output cannot be assigned in always(clk) block: "+lName))})
  }
  
  override def p[T](task : Task[T]):T = task match {
    case GetAssignVarSet => Set(lhand.getname)
    case _ => task.emptyValue
  }
}

case class Case(cond : Expression, body : List[(String, StatementList)]) extends Statement {
  def codeGen(env : Environment) = {
    "case (" + cond.codeGen(env) + ")" + newline +
    wrapTab(body.map((a:(String,StatementList)) => 
      a._1 + ": begin" + newline + wrapTab(a._2.codeGen(env)) + "end").mkString("\n")) + newline +
    "endcase"
  }
  
  override def p[T](task : Task[T]):T = task match {
    case GetAssignVarSet => body.foldLeft(task.emptyValue)((a,b) => task.mergeFunction(a,b._2.p(task)))
    case _ => task.emptyValue
  }
}

case class ForLoop(id : String, init : Expression, cond : Expression, step : Expression, body : StatementList) extends Statement {
  def codeGen(env : Environment) = {
    println("For loop discarded.");
    ""
  }
}

case class Debug(cmd : String) extends Statement {
  def codeGen(env : Environment) = {
    println("Debug command discarded: " + cmd);
    ""
  }
}

class StatementList(val stmts : List[Statement]) extends VerilogASTNode {
  def codeGen(env : Environment) = stmts.map(_.codeGen(env)).mkString("\n")
  
  def semCheck(moduleArgs : List[String], isAlwaysClk : Boolean) = stmts.foreach(_.semCheck(moduleArgs, isAlwaysClk))
  
  def p[T](task : Task[T]):T = stmts.foldLeft(task.emptyValue)((a,b) => task.mergeFunction(a,b.p(task)))
}


/* Expressions" */
sealed abstract class Expression extends VerilogASTNode {
  def codeGen(tag : String) : String 
  def codeGen(env : Environment) = codeGen("")
}

trait Lvalue extends Expression {
  def getname : String
}

case class Variable(id : String, isRead : Boolean) extends Lvalue {
  def getname = id
  def codeGen(tag : String) = if (Store.params.contains(id)) id else rename(id, tag)
}

case class Number(value : String) extends Expression {
  def codeGen(tag : String) = value
}

case class ArrayExpression(id : String, dim : Expression, isRead : Boolean) extends Lvalue {
  def getname = id
  def codeGen(tag : String) = rename(id, tag) + "[" + dim.codeGen(tag) + "]" + (if (Store.vectors.contains(id)) "[" + Store.vectors(id) + ":0]" else "")
}

case class VectorExpression(id : String, dim1 : Expression, dim2 : Expression, isRead : Boolean) extends Lvalue {
  def getname = id
  def codeGen(tag : String) = rename(id, tag) + "[" + dim1.codeGen(tag) + "][" + dim2.codeGen(tag) + "]"  
}

case class UnaryExpression(expr : Expression, op : String) extends Expression {
  def codeGen(tag : String) = op + expr.codeGen(tag)
}

case class BinaryExpression(expr1 : Expression, expr2 : Expression, op : String) extends Expression { 
  def codeGen(tag : String) = expr1.codeGen(tag) + op + expr2.codeGen(tag)
}

case class TernaryExpression(cond : Expression, ifexpr : Expression, elseexpr : Expression) extends Expression {
  def codeGen(tag : String) = cond.codeGen(tag) + "?" + ifexpr.codeGen(tag) + ":" + elseexpr.codeGen(tag)
}

case class ParenExpression(expr : Expression) extends Expression {
  def codeGen(tag : String) = "(" + expr.codeGen(tag) + ")"
}

case class ConcatExpression(exprs : List[Expression]) extends Expression {
  def codeGen(tag : String) = "{" + exprs.map(_.codeGen(tag)).mkString(",") + "}"
}