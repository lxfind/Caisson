package sta;

//The universal AST node class that all other nodes inherit from
sealed abstract class StaticCaissonASTNode {  	  
	//Put a tab before each line in some code, for indenting purpose
	protected def wrapTab(str : String) : String = str.split(newline).map("\t"+_+"\n").mkString
	
	//A helper function to make the code cleaner: Based on whether a "Some(x)" is None, return different values
	protected def wrapOption[T,R](cond : Option[T], f1 : => R, f2: => R) = (if (cond.isEmpty) f1 else f2)
	
	//Check if generated code is empty
	protected def isEmptyCode(code : Map[String,String]) : Boolean = code.filter(x => !x._1.isEmpty || !x._2.isEmpty()).isEmpty
	
	protected def pickName(a : String, b : String) = 
	  (if (!a.isEmpty && !b.isEmpty) throw new Exception("State "+a+" and "+b+"get mixed up in the same code, which should be caused by multiple falls in single state") 
	  else (if (a.isEmpty) b else a))
	
	protected def wrapDim(dim : Option[Dim], env : Environment) = dim match {
	  case None => ""
	  case Some(d) => d.codeGen(env)
	}
	
	protected val newline = "\n"  	
}

/*
 * Mehods that appear in most nodes:
 * 1. codeGen: Code Generation. mostly (except Program) takes environment and mode (either Clock or Star) as arguments, generates a mapping from leaf state name to the corresponding code.
 * The reason that codeGen returns a mapping instead of a single string is because "fall" commands will return the code of all child states, which, when propogated to the top, will become
 * a mapping from each leaf state to the code that goes all the way down from the top of the state hierarchy to the bottom.  
 * 
 * 2. caissonType: Type Check, implementing all typing rules.
 * 
 * 3. p: A generic function appearing in each node that performs certain task and automatically pass the task down the code tree. 
 * The reason to have it is because I don't want to write a different method for each node every time I want to collect some information or verify some constrains recursively.
 * All tasks are defined in Environment.scala
 * 
 */

class Program(name: String, params: List[String], decl: List[Declaration], defn: StateDefinition, parameters: List[Parameter], assigns : List[Assign], instances: List[Instance], reset: StatementList) extends StaticCaissonASTNode {
  def computeEnvironment(isMain : Boolean): Environment = {        
    val gotoMap = defn.p(GetGotos).groupBy(_._1).mapValues(_.map(_._2).remove(_.isEmpty)) // Get all goto information: a map from state name to all argument lists used in goto that state 	
    val stateMap = defn.getStates(0, gotoMap)._2	// Get all state information: a map from state name to StateInfo       
    val symbolTable = decl.flatMap(_.getSymbols).toMap ++ parameters.map(x => (x.name->new SymbolInfo()))	// Get all symbols defined in declarations and parameters
    // Add all parameterized symbols to the symbol table
    val fullSymbolTable = symbolTable ++ stateMap.flatMap(x => {
      val args = x._2.args    
      args.indices.map(i => {    
        val s = symbolTable(gotoMap(x._1)(0)(i))     
        (args(i)._1 -> new SymbolInfo(s.datatype, s.dim1, s.dim2, args(i)._2, s.isSigned, true, gotoMap(x._1).map(_(i)), x._1))
    })}).toMap
    val assignSet = defn.p(GetAssignVarSet)	// Get all variables that are getting written in the code
    val readSet = defn.p(GetReadVarSet)	// Get all variables that are getting read in the code
   
    new Environment(fullSymbolTable, stateMap, assignSet, readSet, isMain)
  }
  
  def caissonType(env: Environment, kappa: DirectedLatticeGraph) = defn.caissonType(env, kappa) //implements T-PROG
  
  def p[T](task : Task[T]):T = task.mergeFunction(task.mergeFunction(decl.foldLeft(task.emptyValue)((a,b) => task.mergeFunction(a,b.p(task))), defn.p(task)), parameters.foldLeft(task.emptyValue)((a,b) => task.mergeFunction(a,b.p(task))))
  
  def codeGen(env : Environment) = {
    val extra = env.getExtra    
    val starCode = defn.codeGen(env, Star)
    val clkCode = defn.codeGen(env, Clk)
    val fullStarCode = extra._6 + wrapSM(starCode, env)
    val fullClkCode = extra._5 + wrapSM(clkCode, env)
    
    "module " + name + "(" + (params++extra._1).mkString(",") + ");" + newline +
    parameters.map(_.codeGen(env)).mkString +
    (decl++extra._2).map(_.codeGen(env)).mkString +    
    (assigns++extra._3).map(_.codeGen(env)).mkString + newline +
    (if (fullStarCode.isEmpty) "" else "always @(*) begin" + newline + wrapTab(fullStarCode) + "end" + newline) +
    (if (fullClkCode.isEmpty && reset.stmts.isEmpty && extra._4.isEmpty) "" else "always @(posedge clk or posedge reset) begin" + newline + 
        wrapTab("if (reset) begin" + newline +
            wrapTab(reset.codeGen(env, Clk, null).first._2 + extra._4) +              
            "end else begin"+newline+wrapTab(fullClkCode)+"end"+newline) + "end" + newline) +
    instances.map(_.codeGen(env)).mkString +
    "endmodule"
  }
  
  // Wrap all state code into a state machine
  private def wrapSM(code : Map[String,String], env: Environment) = (if (code.toList.exists(!_._2.isEmpty)) 
        "case (cur_state)" + newline +
        wrapTab(code.map(x => (x._1->(x._2,env.stateTable(x._1)))).values.toSeq.sortBy(_._2.id).map(x => {
          x._2.id.toString + ": begin" + newline +
          wrapTab(x._1) + "end" + newline
        }).mkString) + "endcase" + newline
      else "")
  
}

class StateDefinition(val name: String, secLevel: String, val paramAndTypeList: List[(String, String)], constraintList: Option[List[(String,String)]], states : Option[List[StateDefinition]], stmts : StatementList) extends StaticCaissonASTNode{      
  // Get all state information. The integer in the return value is used to assign unique ID to each leaf state. For non-leaf states, their ID will be the ID of the default child.
  def getStates(id : Int, gotoMap : Map[String,List[List[String]]]) : (Int, Map[String,StateInfo]) = {
    val sectype = new StateType(SimpleType(secLevel), paramAndTypeList.map(x => SimpleType(x._2)), wrapOption(constraintList, List(), constraintList.get.map(x => (SimpleType(x._1),SimpleType(x._2)))))
    val fall = stmts.p(GetFall)    
    val children = wrapOption(states, List(), states.get.map(_.name))
    wrapOption(states, (id+1, Map(name->new StateInfo(name, sectype, paramAndTypeList, true, id, gotoMap(name).size, fall, children))), ({
      val ret = states.get.foldLeft((id, Map[String, StateInfo]()))((a,b) => {
        val temp = b.getStates(a._1, gotoMap)
        (temp._1, a._2++temp._2)
      })
      (ret._1, ret._2 ++ Map(name -> new StateInfo(name, sectype, paramAndTypeList, false, ret._2(states.get(0).name).id, gotoMap(name).size, fall, children)))
    }))
  } 
  
  def p[T](task : Task[T]):T = {
    val stateRet = wrapOption(states, task.emptyValue, states.get.map(_.p(task)).reduce(task.mergeFunction))
    val stmtRet = stmts.p(task)
    task.mergeFunction(task.mergeFunction(stateRet, stmtRet),
   (task match {
     case GetGotos => List((name, List()))
     case DupNameCheck => (List((name,secLevel))++paramAndTypeList).map(x=> (Set(x._1),Set(x._2))).reduce(task.mergeFunction)
     case DefaultChildNoParamCheck => if (states.isDefined && !states.get(0).paramAndTypeList.isEmpty) throw new Exception("Default child state should not take parameters:"+states.get(0).name) else task.emptyValue
     case EndWithGotoFallCheck => if (!stmts.p(task)) throw new Exception("Statements in state "+name+" does not end with a goto/fall") else false
     case LeafNoFallCheck => if (this.states.isEmpty && stmts.p(task)) throw new Exception("Leaf state "+name+" should not contain fall") else false
     case GotoSameLevelCheck => if (stateRet._2.forall(states.get.map(_.name).contains(_))) (false,stmtRet._2) else throw new Exception("Child states of "+name+" contains goto that targets at states not within the same level") 
     case _ => task.emptyValue
   }))
  }  
  
  // Generate corresponding code for each leaf state
  def codeGen(env : Environment, mode : AlwaysType) : Map[String, String] = {
    val stateCode = wrapOption(states, Map(), states.get.flatMap(_.codeGen(env, mode)).toMap)     
    wrapOption(states, Map(name->stmts.codeGen(env, mode, Map()).values.first), {val x =stmts.codeGen(env, mode, states.get.flatMap(_.codeGen(env, mode)).toMap); x}) 
  }
  
  def caissonType(env: Environment, kappa: DirectedLatticeGraph): StateType = { 
    val stateType = env.typeMap(name).asInstanceOf[StateType]
    val defnType = stmts.caissonType(env, kappa)
    if (states.isDefined) states.get.foreach(_.caissonType(env, kappa))	//implements T-DEF
    if (kappa.isConnected(stateType.level.level, defnType.level.level)) stateType //implements T-STATE
    else throw new CaissonTypeException("State type mismatch: "+stateType.level.level+" does not match "+defnType.level.level+" in state "+name)
  }
}

class Module(name : String, args : List[String], blocks : List[Block])
case class Always(alwaysType : AlwaysType, stmts : StatementList) extends Block
case class Initial(stmts : StatementList) extends Block

sealed abstract class Block extends StaticCaissonASTNode

case class Assign(lhand : Expression, rhand : Expression) extends Block {
  def this(lvar : String, condVar : String, condValue : Int, value : String) = 
    this(Variable(lvar, true), new TernaryExpression(condVar, condValue, value, Number("0")))
  
  def codeGen(env : Environment) = "assign "+lhand.codeGen(env, null)+" = "+rhand.codeGen(env, null) + ";" + newline
}

case class Instance(moduleName : String, instName : String, args : List[(String,Expression)]) extends Block {
  def codeGen(env : Environment) = {
    val extraParam = List(("cur_state",Variable("cur_state", true))) ++ env.getGotoStates.map(x => ("cond_"+x.name, Variable("cond_"+x.name, true)))
    moduleName + " " + instName + "(" + (args++extraParam).map(x => "."+x._1+"("+x._2.codeGen(env, null)+")").mkString(",")+");" + newline
  }
}

/* Parameters */
case class Parameter(name : String, value : Expression) extends Block {
  def codeGen(env : Environment) = "parameter " + name + " = " + value.codeGen(env, null) + ";" + newline
  
  def p[T](task : Task[T]):T = task match {
    case DupNameCheck => (Set(name), Set())
    case _ => task.emptyValue
  }
}

/* Declarations */
case class Declaration(datatype : DataType, isSigned : Boolean, dim : Option[Dim], decs : List[SingleDec])  extends Block {
  def this(datatype : DataType, name : String, symb : SymbolInfo) = this(datatype, symb.isSigned, symb.dim1, List(new SingleDec(name, symb.dim2)))
  def this(datatype : DataType, name : String, num : Int) = this(datatype, false, Util.dimGen(num), List(new SingleDec(name, None)))
  def this(datatype : DataType, name : String) = this(datatype, false, None, List(new SingleDec(name, None)))
  
  def getSymbols = decs.flatMap((x) => List((x.id, new SymbolInfo(datatype, dim, x.dim, x.level, isSigned))))
  
  def codeGen(env : Environment) = {
    val t = datatype match {
      case Wire => List("wire")
      case Register => List("reg")
      case Input => List("input")
      case Output => List("output")     
      case Integer => List("integer")
    }    
    t.map(_ + wrapDim(dim, env) + " " + decs.map(_.codeGen(env)).mkString(",") + ";" + newline).mkString
  }
  
  def p[T](task : Task[T]):T = task match {
    case DupNameCheck => decs.map(x => (Set(x.id),Set(x.level))).reduce(task.mergeFunction)
    case _ => task.emptyValue
  }
} 

case class SingleDec(val id : String, val dim : Option[Dim], val level : String) extends StaticCaissonASTNode {  
  def isVector = dim.isDefined
  
  def this(id : String, dim : Option[Dim]) = this(id, dim, null)
  
  def codeGen(env : Environment) = id + wrapDim(dim, env)
}

/* Dimension */
sealed abstract class Dim extends StaticCaissonASTNode {
  def codeGen(env : Environment) : String
}

case class SingleDim(size : Expression) extends Dim {
  def codeGen(env : Environment) = "[" + size.codeGen(env, null) + "]"
} 

case class DoubleDim(range1 : Expression, range2 : Expression) extends Dim {
  def codeGen(env : Environment) = "[" + range1.codeGen(env, null) + ":" + range2.codeGen(env, null) + "]"
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
sealed abstract class Statement extends StaticCaissonASTNode {  
  def p[T](task : Task[T]):T = task.emptyValue
  def codeGen(env : Environment, mode : AlwaysType, children : Map[String, String]) : Map[String, String] = Map()
  def caissonType(env: Environment, kappa: DirectedLatticeGraph): CommandType = CommandType(SimpleType("H"))
  
}

case class Conditional(cond : Expression, ifstmts : StatementList, elsestmts : Option[StatementList]) extends Statement {
  override def p[T](task : Task[T]):T = task.mergeFunction(task.mergeFunction(task.mergeFunction(cond.p(task), ifstmts.p(task)), wrapOption(elsestmts, task.emptyValue, elsestmts.get.p(task))), task match {
    case BranchGotoFallCheck => if (ifstmts.p(task) != (elsestmts.isDefined && elsestmts.get.p(task))) throw new Exception("fall/goto in branches should be consistent.") else task.emptyValue
    case EndWithGotoFallCheck => ifstmts.p(task)
    case _ => task.emptyValue
  })
  
  override def codeGen(env : Environment, mode : AlwaysType, children : Map[String, String]) = {
    val ifcode = ifstmts.codeGen(env, mode, children)
    val elsecode = wrapOption(elsestmts, Map(""->""), elsestmts.get.codeGen(env, mode, children))    
    (if (isEmptyCode(ifcode) && isEmptyCode(elsecode)) Map(""->"") else
      for (a <- ifcode; b <- elsecode) yield ((if (a._1.isEmpty) b._1 else a._1)-> 
      	("if (" + cond.codeGen(env, mode) + ") begin" + newline +
      	wrapTab(a._2) +
      	"end" + (if (b._2.isEmpty) newline else (" else begin" + newline + 
      	wrapTab(b._2) + 
      	"end" + newline))))) 
  }
  
  override def caissonType(env: Environment, kappa: DirectedLatticeGraph): CommandType = { //implements T-IF
    val condType = cond.caissonType(env, kappa)
    val thenBodyType = ifstmts.caissonType(env, kappa).level
    val elseBodyType = wrapOption(elsestmts, thenBodyType, elsestmts.get.caissonType(env, kappa).level)    
    val bodyType = TypeUtil.meet(kappa, thenBodyType, elseBodyType)
    if (kappa.isConnected(condType.level, bodyType.level)) CommandType(bodyType)
    else throw new CaissonTypeException("Illegal assignments in higher contexts")
  }
} 

case class NonBlockAssign(lhand : Lvalue, rhand : Expression) extends Statement {  
  override def p[T](task : Task[T]):T = task.mergeFunction(lhand.p(task), rhand.p(task))
   
  override def codeGen(env : Environment, mode : AlwaysType, children : Map[String, String]) = {
    val lcode = lhand.codeGen(env, mode)
    val rcode = rhand.codeGen(env, mode)
    val code = if (lcode.isEmpty) "" else lhand match {
      case v:VectorExpression => {
        val names = env.symbolTable(v.id).realNames
        "case (cond_"+env.symbolTable(v.id).ownerState+")"+newline+wrapTab(names.indices.map(i => i +": begin " +names(i)+lcode+" <= "+rcode +"; end" +newline).mkString) +"endcase" + newline
      }
      case _ => lcode + " <= " + rcode + ";" + newline 
    } 
    Map("" -> code)
  } 
  
  override def caissonType(env: Environment, kappa: DirectedLatticeGraph): CommandType = { //implements T-ASSIGN
    val rvalueType = rhand.caissonType(env, kappa)
    val lvalueType = lhand.caissonType(env, kappa)    
    val wtype = env.typeMap(lhand.getID).asInstanceOf[SimpleType]
    if (kappa.isConnected(TypeUtil.join(kappa, rvalueType, lvalueType).level, wtype.level)) CommandType(wtype) else throw new CaissonTypeException("Cannot perform assignment to "+lhand.getID+": Incompatible value on right hand side")
  }
  
}

case class Case(cond : Expression, body : List[(String, StatementList)]) extends Statement {
  override def p[T](task : Task[T]):T = task.mergeFunction(cond.p(task), body.map(_._2.p(task)).reduce(task.mergeFunction))
  
  override def codeGen(env : Environment, mode : AlwaysType, children : Map[String,String]) = {
    val head = "case (" + cond.codeGen(env, mode) + ")" + newline
    val bodyCode = body.map(x => (x._1, x._2.codeGen(env, mode, children)))    
    if (bodyCode.remove(x => isEmptyCode(x._2)).isEmpty) Map(""->"") else
    bodyCode.foldLeft(Map(""->head))((a,b) => for (x<-a;y<-b._2) yield (pickName(x._1,y._1)-> (x._2 + wrapTab(b._1 + ": begin" + newline + wrapTab(y._2) + "end" + newline)))).mapValues(_ + "endcase" + newline)
  }
  
  override def caissonType(env: Environment, kappa: DirectedLatticeGraph): CommandType = { //implements T-CASE
    val condType = cond.caissonType(env, kappa)
    val bodyTypeList = body.map(_._2.caissonType(env, kappa).level)
    val bodyTypeLevel = bodyTypeList.foldLeft(SimpleType("H"))((t1: SimpleType, t2: SimpleType) => TypeUtil.meet(kappa, t1, t2))
    if(kappa.isConnected(condType.level, bodyTypeLevel.level)) CommandType(bodyTypeLevel)
    else throw new CaissonTypeException("Case statements not typeable")
  }
} 

case class ForLoop(id : String, init : Expression, cond : Expression, step : Expression, body : StatementList) extends Statement
case class Debug(cmd : String) extends Statement

case class Fall extends Statement {
  override def p[T](task : Task[T]):T = task match {
    case GetFall => this
    case BranchGotoFallCheck | EndWithGotoFallCheck | LeafNoFallCheck => true
    case _ => super.p(task)
  }
  
  override def codeGen(env : Environment, mode : AlwaysType, children : Map[String, String]) = children
  
  override def caissonType(env: Environment, kappa: DirectedLatticeGraph): CommandType = { //implements T-FALL    
    val state = env.stateTable.find(_._2.fall==(this)).get._2
    val stateLevel = state.sectype.level    
    val defaultChildCommandLevel = env.typeMap(state.children(0)).asInstanceOf[StateType].level
    if (kappa.isConnected(stateLevel.level, defaultChildCommandLevel.level)) CommandType(stateLevel)
    else throw new CaissonTypeException("Illegal fall")
  }
}

case class Jump(target: String, argList: List[String]) extends Statement {
  override def codeGen(env : Environment, mode : AlwaysType, children : Map[String, String]) = {
    if (env.isMain && mode.equals(Star)) Map("" -> {
      val state = env.stateTable(target)      
      "cur_state_w <= "+state.id.toString + ";" + newline + (if (argList.isEmpty) "" else "cond_"+target+"_w <= "+env.symbolTable(state.args(0)._1).realNames.indexOf(argList(0)) +";"+newline)
    }) else Map(""->"")       
  }
  
  override def p[T](task : Task[T]):T = task match {
    case GetGotos => if (argList.isEmpty) List() else List((target, argList))
    case BranchGotoFallCheck | EndWithGotoFallCheck => true
    case GotoSameLevelCheck => (true, List(target))
    case _ => task.emptyValue
  }
  
  override def caissonType(env: Environment, kappa: DirectedLatticeGraph): CommandType = { //implements T-GOTO    
    val targetStateType = env.typeMap(target).asInstanceOf[StateType]
    val typeSubstitutionMap = argList.indices.map(i => (targetStateType.paramTypeList(i).level -> env.typeMap(argList(i)).asInstanceOf[SimpleType])).toMap
    val sourceType = Util.substituteType(targetStateType.level, typeSubstitutionMap)
    val substitutedConstraints = Util.substituteConstraints(targetStateType.constraints, typeSubstitutionMap)
    if (substitutedConstraints.forall((x: (SimpleType, SimpleType)) => kappa.isConnected(x._1.level, x._2.level))) CommandType(sourceType)
    else throw new CaissonTypeException("Illegal goto")
  }
}

case class StatementList(stmts : List[Statement]) extends StaticCaissonASTNode {
  def p[T](task : Task[T]):T = stmts.map(_.p(task)).foldLeft(task.emptyValue)(task.mergeFunction)
  
  def codeGen(env : Environment, mode : AlwaysType, children : Map[String, String]) : Map[String, String] = {
    val code = stmts.map(_.codeGen(env, mode, children))  
    if (code.isEmpty) Map("" -> "") else code.reduceLeft((x,y) => 
     for (a <- x; b <- y) yield (if (a._1.isEmpty) (b._1->(a._2+b._2)) else (a._1->(a._2+b._2)))) 
  }
   
  def caissonType(env: Environment, kappa: DirectedLatticeGraph): CommandType = { //implements T-SEQ
    CommandType(stmts.foldLeft(SimpleType("H"))((t: SimpleType, s: Statement) => TypeUtil.meet(kappa, t, s.caissonType(env, kappa).level)))
  }
} 

/* Expressions" */
sealed abstract class Expression extends StaticCaissonASTNode {
  def p[T](task : Task[T]):T
  def codeGen(env : Environment, mode : AlwaysType) : String
  def caissonType(env: Environment, kappa: DirectedLatticeGraph) : SimpleType
}

trait Lvalue extends Expression {
  def getID : String
}

case class Variable(val id : String, val isRead : Boolean) extends Lvalue {
  def codeGen(env : Environment, mode : AlwaysType) = if (isRead) id else mode match {
    case Star => if (env.symbolTable(id).isParam) id+"_w" else if (env.symbolTable(id).datatype.equals(Register)) "" else id 
    case Clk => if (env.symbolTable(id).isParam) "" else if (env.symbolTable(id).datatype.equals(Register)) id else ""
  } 
  
  def p[T](task : Task[T]):T = task.mergeFunction(task.emptyValue, task match {
    case GetAssignVarSet => if (isRead) task.emptyValue else Set(this.id)
    case GetReadVarSet => if (!isRead) task.emptyValue else Set(this.id)
    case _ => task.emptyValue
  })
  
  def caissonType(env: Environment, kappa: DirectedLatticeGraph) = env.typeMap(id).asInstanceOf[SimpleType]
  
  def getID = id
}

case class Number(value : String) extends Expression {
  def codeGen(env : Environment, mode : AlwaysType) = value
  def p[T](task : Task[T]):T = task.emptyValue
  def caissonType(env: Environment, kappa: DirectedLatticeGraph) = SimpleType("L")
}

case class ArrayExpression(val id : String, dim : Expression, isRead : Boolean) extends Lvalue {
  def codeGen(env : Environment, mode : AlwaysType) = if (!isRead && env.symbolTable(id).isParam && mode.equals(Clk)) "" else
    (if (isRead || !env.symbolTable(id).isParam) id else id+"_w") + "[" + dim.codeGen(env, mode) + "]"
  
  def p[T](task : Task[T]):T = task.mergeFunction(dim.p(task), task match {
    case GetAssignVarSet => if (isRead) task.emptyValue else Set(this.id)
    case GetReadVarSet => if (!isRead) task.emptyValue else Set(this.id)
    case _ => task.emptyValue
  })
  
  def getID = id
  
  def caissonType(env: Environment, kappa: DirectedLatticeGraph) = TypeUtil.join(kappa, env.typeMap(id).asInstanceOf[SimpleType], dim.caissonType(env, kappa))
}

case class VectorExpression(val id : String, dim1 : Expression, dim2 : Expression, isRead : Boolean) extends Lvalue {
  def p[T](task : Task[T]):T = task.mergeFunction(task.mergeFunction(dim1.p(task), dim2.p(task)), (task match {
    case GetAssignVarSet => if (isRead) task.emptyValue else Set(this.id)
    case GetReadVarSet => if (!isRead) task.emptyValue else Set(this.id)
    case GetVectors => List((isRead, this, getWidth))
    case _ => task.emptyValue
  }))
  
  def codeGen(env : Environment, mode : AlwaysType) = {
    val dims = "[" + dim1.codeGen(env, mode) + "][" + dim2.codeGen(env, mode) + "]"
    if (!env.symbolTable(id).isParam) if (isRead || mode.equals(Clk)) (id + dims) else ""
    else if (isRead) Util.ternaryGen("cond_"+env.symbolTable(id).ownerState, env.symbolTable(id).realNames).codeGen(env, mode).replace(":",dims+":")+dims
    			else if (mode.equals(Star)) "" else dims    
  }
  
  // Get the width of the last dimension
  private def getWidth : Int = {
    dim2 match {
      case _:Number => 1
      case b:BinaryExpression => if (b.expr1.isInstanceOf[Number] && b.expr2.isInstanceOf[Number] && b.op.equals(":")) 
        math.abs(b.expr1.asInstanceOf[Number].value.toInt - b.expr2.asInstanceOf[Number].value.toInt) + 1 else throw new Exception("The second Dimention of a vector expression must has constance width: "+this.id)
      case _ => throw new Exception("Sorry man but the getWidth method can only be applied to dimention that has fixed width: "+this)
    }
  }
  
  def getID = id
  
  def caissonType(env: Environment, kappa: DirectedLatticeGraph) = TypeUtil.join(kappa, env.typeMap(id).asInstanceOf[SimpleType], TypeUtil.join(kappa, dim1.caissonType(env, kappa), dim2.caissonType(env, kappa)))
}

case class UnaryExpression(expr : Expression, op : String) extends Expression {
  def p[T](task : Task[T]):T = expr.p(task)
  def codeGen(env : Environment, mode : AlwaysType) = op + expr.codeGen(env, mode)
  def caissonType(env: Environment, kappa: DirectedLatticeGraph) = expr.caissonType(env, kappa)
}

case class BinaryExpression(expr1 : Expression, expr2 : Expression, op : String) extends Expression {
  def p[T](task : Task[T]):T = task.mergeFunction(expr1.p(task), expr2.p(task))
  def codeGen(env : Environment, mode : AlwaysType) = expr1.codeGen(env, mode) + op + expr2.codeGen(env, mode)
  def caissonType(env: Environment, kappa: DirectedLatticeGraph) = TypeUtil.join(kappa, expr1.caissonType(env, kappa), expr2.caissonType(env, kappa))
} 

case class TernaryExpression(cond : Expression, ifexpr : Expression, elseexpr : Expression) extends Expression {
  def p[T](task : Task[T]):T = task.mergeFunction(cond.p(task), task.mergeFunction(ifexpr.p(task), elseexpr.p(task)))
  
  def this(condVar : String, condValue : Int, ifValue : String, elseValue : Expression) = 
    this(BinaryExpression(Variable(condVar, true), Number(condValue.toString), "=="), Variable(ifValue, true), elseValue)
  
  def codeGen(env : Environment, mode : AlwaysType) = cond.codeGen(env, mode) + "?" + ifexpr.codeGen(env, mode) + ":" + elseexpr.codeGen(env, mode)
  
  def caissonType(env: Environment, kappa: DirectedLatticeGraph) = TypeUtil.join(kappa, TypeUtil.join(kappa, ifexpr.caissonType(env, kappa), elseexpr.caissonType(env, kappa)), cond.caissonType(env, kappa))
} 

case class ParenExpression(expr : Expression) extends Expression {
  def p[T](task : Task[T]):T = expr.p(task)
  def codeGen(env : Environment, mode : AlwaysType) = "(" + expr.codeGen(env, mode) + ")"
  def caissonType(env: Environment, kappa: DirectedLatticeGraph) = expr.caissonType(env, kappa)
}

case class ConcatExpression(exprs : List[Expression]) extends Expression {
  def p[T](task : Task[T]):T = exprs.map(_.p(task)).reduce(task.mergeFunction)
  def codeGen(env : Environment, mode : AlwaysType) = "{" + exprs.map(_.codeGen(env, mode)).mkString(",") + "}"
  def caissonType(env: Environment, kappa: DirectedLatticeGraph) = exprs.map(_.caissonType(env, kappa)).reduce((a,b) => TypeUtil.join(kappa, a, b))
}