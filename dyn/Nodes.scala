
/*
 Please refer to licensing information in LICENSE.txt
 Author: Vineeth Kashyap
 Email: vineeth@cs.ucsb.edu
 This file defines the Abstract Syntax Tree for Dynamic Caisson Programs.
*/
package dyn

sealed abstract class CaissonASTNode { //all AST Nodes inherit from these
}

abstract class Expr extends CaissonASTNode {
  def getTags = Set.empty[Tag] //empty by default

  def genCode(ci: CompilerInternals): String
}

case class Number(value: String) extends Expr {
  override def genCode(ci: CompilerInternals) = value
}


case class Variable(name: String) extends Expr {
  override def getTags = Set(StateOrRegisterReferenceTag(name))

  def getName = name

  override def genCode(ci: CompilerInternals) = name
}

case class ComplexExpr(left: Expr, right: Expr, op: String) extends Expr {
  override def getTags = left.getTags ++ right.getTags

  override def genCode(ci: CompilerInternals) = left.genCode(ci) + op + right.genCode(ci)
}

case class UnaryExpr(operator: String, operand: Expr) extends Expr {
  override def getTags = operand.getTags

  override def genCode(ci: CompilerInternals) = operator + operand.genCode(ci)
}

case class ArrayExpr(name: Variable, dimension1: Expr, dimension2: Option[Expr]) extends Expr {
  override def getTags = Set(RegisterArrayReferenceTag(this)) ++ dimensionTags

  def registerName = name.getName

  def dimensionTags = dimension1.getTags ++  ( dimension2 match {
    case Some(e) => e.getTags
    case None => Set[Tag]()
  } )

  def dimensionGenCode(ci: CompilerInternals) = {
    "[" + dimension1.genCode(ci) + "]" + (dimension2 match {
      case Some(x) => "[" + x.genCode(ci) + "]"
      case None => ""
    })
  }

  override def genCode(ci: CompilerInternals) = name.genCode(ci) + dimensionGenCode(ci)

  def genTagCode(ci: CompilerInternals) = name.genCode(ci) + "_tag" + dimensionGenCode(ci)

}

case class SingularCollection(singularList: List[Expr]) extends Expr {
  override def getTags = singularList.foldLeft(Set.empty[Tag]) {
    (s, e) => s ++ e.getTags
  }

  override def genCode(ci: CompilerInternals): String = {
    "{" + singularList.map((e) => e.genCode(ci)).mkString(", ") + "}"
  }
}

sealed abstract class Statement extends CaissonASTNode {

  def dynamicCheckTransform(rmap: KindEnvironment): Statement = this //default behavior

//  def assignmentSummary(ci: CompilerInternals,
//                        state: String): (Set[String], Set[String]) = (Set.empty[String], Set.empty[String]) //default

//  def computeDynamicUpdateRegisters(assignmentSummaryMap: Map[String, Set[String]],
//                                    rmap: KindEnvironment,
//                                    fallGraph: Map[String, List[String]],
//                                    state: String): Set[String] = {
//    Set.empty[String] //default
//  }

  def assignmentSummary(ci: CompilerInternals): Set[String] = Set.empty[String]

  def genCode(ci: CompilerInternals): String

  def getConditionTags: Set[Tag] = Set.empty[Tag]
}

case class Assignment(lvalue: Expr, rvalue: Expr, otherwise: Option[Command]) extends Statement {

  override def dynamicCheckTransform(rmap: KindEnvironment): Statement = {
    val lhsTagSet = lvalue match {
      case Variable(reg) if (rmap.fixedRegisters.contains(reg)) => lvalue.getTags //fixed register, get tags for lvalue
      case ae @ ArrayExpr(Variable(regArray), d1, d2) if (rmap.fixedRegisters.contains(regArray)) =>
        Set(RegisterArrayReferenceTag(ae))
      case _ => Set[Tag]()
    }
    if (lhsTagSet.isEmpty) this; //we are not writing to fixed register
    else {
      assert(lhsTagSet.size == 1) //should be true by construction
      val lhsTag = lhsTagSet.head
      val rhsTagSet = rvalue.getTags ++ Set(PC()) ++ (lhsTag match {
        case RegisterArrayReferenceTag(ae) => ae.dimensionTags
        case _ => Set.empty[Tag]
      })
      val condition = GreaterThanTag(lhsTag, JoinTag(rhsTagSet))
      val elseBody = otherwise match {
        case Some(cmd) => Some(cmd.dynamicCheckTransform(rmap))
        case None => Some(Command(List(Skip()))) //default otherwise case
      }
      Branch(condition, Command(List(Assignment(lvalue, rvalue, None))), elseBody)
    }
  }

//  override def assignmentSummary(ci: CompilerInternals,
//                                 state: String): (Set[String], Set[String]) = {
//    (lvalue match {
//      case Variable(reg) if (ci.kindMapping.fixedRegisters.contains(reg)) => Set(reg)
//      case ae @ ArrayExpr(Variable(regArray), d1, d2) if (ci.kindMapping.fixedRegisters.contains(regArray)) => Set(regArray)
//      case _ => Set.empty[String]
//    }, Set.empty[String])
//  }

//  override def computeDynamicUpdateRegisters(assignmentSummaryMap: Map[String, Set[String]],
//                                             rmap: KindEnvironment,
//                                             fallGraph: Map[String, List[String]],
//                                             state: String): Set[String] = {
//    assignmentSummary(rmap, Map.empty[String, List[String]], state)._1
//  }

  override def assignmentSummary(ci: CompilerInternals): Set[String] = {
    lvalue match {
      case Variable(reg) if (ci.kindMapping.dynamicRegisters.contains(reg)) => Set(reg)
      case ae @ ArrayExpr(Variable(regArray), d1, d2) if (ci.kindMapping.dynamicRegisters.contains(regArray)) => Set(regArray)
      case _ => Set.empty[String]
    }
  }

  override def genCode(ci: CompilerInternals) = {
    val lvalueName = (lvalue match {
      case Variable(reg) => reg
      case ArrayExpr(Variable(regArray), d1, d2) => regArray
      case _ => throw new CaissonCompilerException("lvalue of an assignment is erroneous")
    })
    val code = lvalue.genCode(ci) + " <= " + rvalue.genCode(ci) + ";\n"
    val update = lvalue.getTags.head.genCode(ci) + " <= " + rvalue.getTags.map(_.genCode(ci)).mkString(" | ") +
      " | " + ci.PCStack.top.genCode(ci) + ";\n"

    ci.codeGenMode match {
      case Star() => {
        if (ci.kindMapping.dynamicRegisters.contains(lvalueName)
          && ci.kindMapping.dynamicRegisters(lvalueName).getDataStructure.dataType.isInstanceOf[RegStar])
          update + code
        else if (ci.kindMapping.fixedRegisters.contains(lvalueName)
          && ci.kindMapping.fixedRegisters(lvalueName).getDataStructure.dataType.isInstanceOf[RegStar])
          code
        else ""
      }
      case PosEdge() => {
        if (ci.kindMapping.dynamicRegisters.contains(lvalueName)
          && ci.kindMapping.dynamicRegisters(lvalueName).getDataStructure.dataType.isInstanceOf[RegPosClk])
          update + code
        else if (ci.kindMapping.fixedRegisters.contains(lvalueName)
          && ci.kindMapping.fixedRegisters(lvalueName).getDataStructure.dataType.isInstanceOf[RegPosClk])
          code
        else ""
      }
      case NegEdge() =>  {
        if (ci.kindMapping.dynamicRegisters.contains(lvalueName)
          && ci.kindMapping.dynamicRegisters(lvalueName).getDataStructure.dataType.isInstanceOf[RegNegClk])
          update + code
        else if (ci.kindMapping.fixedRegisters.contains(lvalueName)
          && ci.kindMapping.fixedRegisters(lvalueName).getDataStructure.dataType.isInstanceOf[RegNegClk])
          code
        else ""
      }
    }
  }
}

//TODO: zero out registers
case class SetStateTag(name: String, level: Tag, otherwise: Option[Command]) extends Statement {
  override def dynamicCheckTransform(rmap: KindEnvironment) = {
    val isFixedState = rmap.fixedRegisters.contains(name)
    if (isFixedState) {
      val condition = ComplexExpr(GreaterThanTag(StateOrRegisterReferenceTag(name), PC()),
                                      GreaterThanTag(level, PC()), "&&")
      val elseBody = otherwise match {
        case Some(cmd) => Some(cmd.dynamicCheckTransform(rmap))
        case None => Some(Command(List(Skip()))) //default otherwise case
      }
      Branch(condition, Command(List(SetStateTag(name, level, None))), elseBody)
    }
    else this
  }

  override def genCode(ci: CompilerInternals) = {
    //assumption: state tags are posedge
    var code = name + "_tag <= " + level.genCode(ci) + "\n"
    ci.codeGenMode match {
      case PosEdge() if (ci.kindMapping.fixedStates.contains(name)) => code
      case _ => ""
    }
  }
}

case class SetRegisterTag(register: String, level: Tag, otherwise: Option[Command]) extends Statement {
  override def dynamicCheckTransform(rmap: KindEnvironment) = {
    //do this only for fixed registers?
    val isFixedRegister = rmap.fixedRegisters.contains(register)
    if (isFixedRegister) {
      val condition = ComplexExpr(GreaterThanTag(StateOrRegisterReferenceTag(register), PC()),
                                  GreaterThanTag(level, PC()), "&&")
      val elseBody = otherwise match {
        case Some(cmd) => Some(cmd.dynamicCheckTransform(rmap))
        case None => Some(Command(List(Skip()))) //default otherwise case
      }
      Branch(condition, Command(List(SetRegisterTag(register, level, None))), elseBody)
    }
    else this
  }

  override def genCode(ci: CompilerInternals) = {
    val code = register + "_tag <= " + level.genCode(ci) + "\n"
    ci.codeGenMode match {
      case Star() if (ci.kindMapping.fixedRegisters.contains(register)
        && ci.kindMapping.fixedRegisters(register).isInstanceOf[RegStar]) => code
      case PosEdge() if (ci.kindMapping.fixedRegisters.contains(register)
        && ci.kindMapping.fixedRegisters(register).isInstanceOf[RegPosClk]) => code
      case NegEdge() if (ci.kindMapping.fixedRegisters.contains(register)
        && ci.kindMapping.fixedRegisters(register).isInstanceOf[RegNegClk]) => code
      case _ => ""
    }
  }
}

case class SetArrayRegisterTag(register: ArrayExpr, level: Tag, otherwise: Option[Command]) extends Statement {
  override def dynamicCheckTransform(rmap: KindEnvironment) = {
    val isFixedRegister = rmap.fixedRegisters.contains(register.registerName)
    if (isFixedRegister) {
      val condition = ComplexExpr(GreaterThanTag(RegisterArrayReferenceTag(register), PC()),
                                  GreaterThanTag(level, JoinTag(register.dimensionTags ++ Set(PC()))), "&&")
      val elseBody = otherwise match {
        case Some(cmd) => Some(cmd.dynamicCheckTransform(rmap))
        case None => Some(Command(List(Skip()))) //default otherwise case
      }
      Branch(condition, Command(List(SetArrayRegisterTag(register, level, None))), elseBody)
    }
    else this
  }

  override def genCode(ci: CompilerInternals) = {
    val code = register.genTagCode(ci) + " <= " + level.genCode(ci)
    val regName = register.registerName
    ci.codeGenMode match {
      case Star() if (ci.kindMapping.fixedRegisters.contains(regName)
        && ci.kindMapping.fixedRegisters(regName).isInstanceOf[RegStar]) => code
      case PosEdge() if (ci.kindMapping.fixedRegisters.contains(regName)
        && ci.kindMapping.fixedRegisters(regName).isInstanceOf[RegPosClk]) => code
      case NegEdge() if (ci.kindMapping.fixedRegisters.contains(regName)
        && ci.kindMapping.fixedRegisters(regName).isInstanceOf[RegNegClk]) => code
      case _ => ""
    }
  }
}

case class Branch(cond: Expr, thenBody: Command, elseBody: Option[Command]) extends Statement {

  override def dynamicCheckTransform(rmap: KindEnvironment) = this

//  override def assignmentSummary(ci: CompilerInternals,
//                                 state: String): (Set[String], Set[String]) = {
//    val thenSummary = thenBody.assignmentSummary(ci, state)
//    val elseSummary = elseBody match {
//      case Some(cmd) => cmd.assignmentSummary(ci, state)
//      case None => (Set.empty[String], Set.empty[String])
//    }
//    (thenSummary._1 ++ elseSummary._1, thenSummary._2 ++ elseSummary._2)
//  }

//  override def computeDynamicUpdateRegisters(assignmentSummaryMap: Map[String, Set[String]],
//                                             rmap: KindEnvironment,
//                                             fallGraph: Map[String, List[String]],
//                                             state: String): Set[String] = {
//    val thenSummary = thenBody.computeDynamicUpdateRegisters(assignmentSummaryMap, rmap, fallGraph, state)
//    val elseSummary = elseBody match {
//      case Some(cmd) => cmd.computeDynamicUpdateRegisters(assignmentSummaryMap, rmap, fallGraph, state)
//      case None => Set.empty[String]
//    }
//    thenSummary ++ elseSummary
//  }

  override def assignmentSummary(ci: CompilerInternals): Set[String] = {
    val thenSummary = thenBody.assignmentSummary(ci)
    val elseSummary = elseBody match {
      case Some(cmd) => cmd.assignmentSummary(ci)
      case None => Set.empty[String]
    }
    thenSummary ++ elseSummary
  }

  override def getConditionTags = cond.getTags

  override def genCode(ci: CompilerInternals) = {
    val topTags = ci.PCStack.top.getTags
    ci.PCStack.push(JoinTag(topTags ++ cond.getTags))
    //update all dynamic variables
    val dynamicVariables = this.assignmentSummary(ci) //TODO: dynamic array variables
    //have array contexts, instead change the array tag code gen
    val dynamicVariablesUpdate = dynamicVariables.map((v) => {
      v + "_tag <= " + ci.PCStack.top.genCode(ci) + ";\n"
    }).mkString
    val thenCode = thenBody.genCode(ci)
    val elseCode = elseBody match {
      case Some(cmd) => cmd.genCode(ci)
      case None => ""
    }
    ci.PCStack.pop()
    if (thenCode != "") {
      dynamicVariablesUpdate +
      "if (" + cond.genCode(ci) + ")\n" +
      "begin\n" +
        thenCode +
      "end\n" +
      (if (elseCode != "")
        ("else begin\n" +
        elseCode +
        "end\n")
       else "")
    }
    else ""
  }
}

case class Kase(cond: Expr, caseMap: Map[List[String], Command]) extends Statement {
  override def dynamicCheckTransform(rmap: KindEnvironment) = this

//  override def assignmentSummary(ci: CompilerInternals,
//                                 state: String): (Set[String], Set[String]) = {
//    caseMap.values.toList.foldLeft((Set.empty[String], Set.empty[String])) {
//      (t, cmd) => {
//        val cmdSummary = cmd.assignmentSummary(ci, state)
//        (t._1 ++ cmdSummary._1, t._2 ++ cmdSummary._2)
//      }
//    }
//  }

//  override def computeDynamicUpdateRegisters(assignmentSummaryMap: Map[String, Set[String]],
//                                             rmap: KindEnvironment,
//                                             fallGraph: Map[String, List[String]],
//                                             state: String): Set[String] = {
//    caseMap.values.toList.foldLeft(Set.empty[String]) {
//      (s, cmd) => {
//        s ++ cmd.computeDynamicUpdateRegisters(assignmentSummaryMap, rmap, fallGraph, state)
//      }
//    }
//  }

  override def assignmentSummary(ci: CompilerInternals): Set[String] = {
    caseMap.values.toList.foldLeft(Set.empty[String]) {
      (t, cmd) => {
        val cmdSummary = cmd.assignmentSummary(ci)
        t ++ cmdSummary
      }
    }
  }

  override def getConditionTags = cond.getTags

  override def genCode(ci: CompilerInternals) = {
    val topTags = ci.PCStack.top.getTags
    ci.PCStack.push(JoinTag(topTags ++ cond.getTags))
    val code = "case (" + cond.genCode(ci) + ")\n" +
    caseMap.keys.toList.map((k: List[String]) => {
      k.mkString(", ") + ": begin\n" +
      caseMap(k).genCode(ci) +
      "end\n"
    }).mkString +
    "endcase\n"
    ci.PCStack.pop()
    code
  }
}

case class Jump(target: String, otherwise: Option[Command]) extends Statement {
  override def dynamicCheckTransform(rmap: KindEnvironment) = this /*{
    //for fixed state, check pc <= fixed_state.tag
    //needs fixed states and dynamic states information, also current state
    val isFixedState = rmap.fixedStates.contains(target)
    val condition = LessThanTag(PC(), StateOrRegisterReferenceTag(target))
  }           */

//  override def assignmentSummary(ci: CompilerInternals,
//                                 state: String): (Set[String], Set[String]) = {
//    (Set.empty[String], Set(target))
//  }

//  override def computeDynamicUpdateRegisters(assignmentSummaryMap: Map[String, Set[String]],
//                                             rmap: KindEnvironment,
//                                             fallGraph: Map[String, List[String]],
//                                             state: String): Set[String] = {
//    assignmentSummaryMap(target)
//  }

  override def assignmentSummary(ci: CompilerInternals): Set[String] = {
    Set.empty[String]
  }

  override def genCode(ci: CompilerInternals) = {
    if (ci.kindMapping.fixedRegisters.contains(target)) { //goto to a fixed state
      //add dynamic check:
      "if (" + ci.PCStack.top + " <= " + target + "_tag)\n" +
      "begin\n" +
      "cur_state <= " + ci.gotoStateIndexMap(target) + ";\n"
      "end\n"
    }
    else { //goto to a non-fixed state
      "cur_state <= " + ci.gotoStateIndexMap(target) + ";\n"
    }
    //assume there are no gotos to non fixed states
    //ci.PCStack.clear()
  }
}

case class Fall(otherwise: Option[Command]) extends Statement {
  override def dynamicCheckTransform(rmap: KindEnvironment) = this

//  override def assignmentSummary(ci: CompilerInternals,
//                                 state: String): (Set[String], Set[String]) = {
//    (Set.empty[String], ci.fallGraph(state).toSet)
//  }

//  override def computeDynamicUpdateRegisters(assignmentSummaryMap: Map[String, Set[String]],
//                                             rmap: KindEnvironment,
//                                             fallGraph: Map[String, List[String]],
//                                             state: String): Set[String] = {
//    //assigmentSummaryMap sets from all possible targets of this fall: which is, all children
//    throw new CaissonCompilerException("Not implemented computeDynamicUpdateRegisters for Fall")
//  }

  override def assignmentSummary(ci: CompilerInternals): Set[String] = {
    Set.empty[String]
  }

  override def genCode(ci: CompilerInternals) = {
    ""
  }
}

case class Skip() extends Statement {
  override def dynamicCheckTransform(rmap: KindEnvironment) = this

  override def genCode(ci: CompilerInternals) = {
    ";\n"
  }
}

sealed abstract class Definition extends CaissonASTNode {
  def dynamicCheckTransform(rmap: KindEnvironment): Definition

//  def assignmentSummary(state: String,
//                        ci: CompilerInternals): Map[String, (Set[String], Set[String])]

  def getStateMap: Map[String, StateDefinition] = Map.empty[String, StateDefinition] //default behavior

  def fallGraph(state: String): Map[String, List[String]] = Map.empty[String, List[String]] //default behavior

  def getFallConditionTags(state: String): Map[String, Set[Tag]] = Map.empty[String, Set[Tag]] //default behavior

  def planarize(accumulator: List[(String, Command)], state: String): Map[String, List[(String, Command)]]
}

case class LetDefinition(stateDefList: List[StateDefinition], cmd: Command)  extends Definition {
  def getStateDefList = stateDefList

  def dynamicCheckTransform(rmap: KindEnvironment) = {
    LetDefinition(stateDefList.map(_.dynamicCheckTransform(rmap)),
      cmd.dynamicCheckTransform(rmap))
  }

//  def assignmentSummary(state: String,
//                        ci: CompilerInternals): Map[String, (Set[String], Set[String])] = {
//    //go into cmd and get all assignments lvalue into first set, all goto/fall targets into second set
//    //fall means all children are possible targets
//    //later get the map from each of the child states
//    stateDefList.foldLeft(Map.empty[String, (Set[String], Set[String])]) {
//      (m, s) => m ++ s.assignmentSummary(ci)
//    } ++
//    cmd.assignmentSummary(state, ci)
//  }

  override def getStateMap: Map[String, StateDefinition] = {
    stateDefList.foldLeft(Map.empty[String, StateDefinition]) {
      (m, s) => {
        m ++ s.getStateMap
      }
    }
  }

  override def fallGraph(state: String): Map[String, List[String]] = {
    Map(state -> stateDefList.map(_.label)) ++
    stateDefList.foldLeft(Map.empty[String, List[String]]) {
      (m, s) => m ++ s.getDefinition.fallGraph(s.label)
    }
  }

  override def getFallConditionTags(state: String) = {
    Map(state -> cmd.lastStatementTags) ++
    stateDefList.foldLeft(Map.empty[String, Set[Tag]]) {
      (m, s) => m ++ s.getDefinition.getFallConditionTags(s.label)
    }
  }

  override def planarize(accumulator: List[(String, Command)], state: String): Map[String, List[(String, Command)]] = {
    stateDefList.foldLeft(Map.empty[String, List[(String, Command)]]) {
      (m, s) => {
        m ++ s.planarize(accumulator ++ List((state, cmd)), state)
      }
    }
  }
}

case class Command(stmtList: List[Statement]) extends Definition {

  def dynamicCheckTransform(rmap: KindEnvironment) = Command(stmtList.map(_.dynamicCheckTransform(rmap)))

//  override def assignmentSummary(state: String,
//                                 ci: CompilerInternals): Map[String, (Set[String], Set[String])] = {
//    Map(state -> stmtList.foldLeft((Set.empty[String], Set.empty[String])) {
//      (t, stmt) => {
//        val stmtSummary = stmt.assignmentSummary(ci, state)
//        (t._1 ++ stmtSummary._1, t._2 ++ stmtSummary._2)
//      }
//    })
//  }

//  def assignmentSummary(ci: CompilerInternals, //when called from branch and case
//                        state: String): (Set[String], Set[String]) = {
//    stmtList.foldLeft((Set.empty[String], Set.empty[String])) {
//      (t, stmt) => {
//        val stmtSummary = stmt.assignmentSummary(ci, state)
//        (t._1 ++ stmtSummary._1, t._2 ++ stmtSummary._2)
//      }
//    }
//  }

//  def computeDynamicUpdateRegisters(assignmentSummaryMap: Map[String, Set[String]],
//                                    rmap: KindEnvironment,
//                                    fallGraph: Map[String, List[String]],
//                                    state: String): Set[String] = {
//    stmtList.foldLeft((Set.empty[String])) {
//      (s, st) => {
//        s ++ st.computeDynamicUpdateRegisters(assignmentSummaryMap, rmap, fallGraph, state)
//      }
//    }
//  }

  def assignmentSummary(ci: CompilerInternals): Set[String] = { //when called from branch and kase
    stmtList.foldLeft(Set.empty[String]) {
      (t, stmt) => {
        val stmtSummary = stmt.assignmentSummary(ci)
        t ++ stmtSummary
      }
    }
  }

  override def planarize(accumulator: List[(String, Command)], state: String): Map[String, List[(String, Command)]] = {
    Map(state -> (accumulator ::: List((state, this))))
  }

  def lastStatementTags: Set[Tag] = stmtList.last.getConditionTags

  def genCode(ci: CompilerInternals) = {
    stmtList.map((stmt) => {
      stmt.genCode(ci)
    }).mkString
  }
}

class StateDefinition(name: String, var level: SecurityLevel, definition: Definition) {
  def label = name

  def getDefinition = definition

  def getLevel = level

  def isFixed: Boolean = level.isInstanceOf[Fixed]

  def dynamicCheckTransform(rmap: KindEnvironment) = {
    new StateDefinition(name, level, definition.dynamicCheckTransform(rmap))
  }

//  def assignmentSummary(ci: CompilerInternals): Map[String, (Set[String], Set[String])] = {
//    definition.assignmentSummary(name, ci)
//  }

  def getStateMap: Map[String, StateDefinition] = {
    Map(name -> this) ++ definition.getStateMap
  }

  def planarize(accumulator: List[(String, Command)], state: String) = {
    definition.planarize(accumulator, name)
  }
}

sealed abstract class DataType {
  def genCode: String

  def isType(s: String): Boolean = false
}
case class Input() extends DataType {
  override def genCode = "input"
}
case class Output() extends DataType {
  override def genCode = "output"
}
case class RegPosClk() extends DataType {
  override def genCode = "reg"

  override def isType(s: String) = s == "pos"
}
case class RegNegClk() extends DataType {
  override def genCode = "reg"

  override def isType(s: String) = s == "neg"
}
case class RegStar() extends DataType {
  override def genCode = "reg"
}
case class Inout() extends DataType {
  def genCode = "inout"
}
case class Imem() extends DataType {
  def genCode = "imem"
}
case class Dmem() extends DataType {
  def genCode = "dmem"
}
case class Wire() extends DataType {
  def genCode = "wire"
}

class DataStructure(dType: DataType, dimension1: Option[(Int, Int)], dimension2: Option[(Int, Int)]) {
  def this(ds: DataStructure, dim2: Option[(Int, Int)]) = this(ds.dataType, ds.dim1, dim2)
  
  def dataType = dType
  
  def dim1 = dimension1

  def dim2 = dimension2

  def getMaxIndex = dimension1 match {
    case Some(x) => x._1
    case None => throw new CaissonCompilerException("Should not call max index on a non-array")
  }

  def genTypeCode = dType.genCode

  def genFirstDimensionCode = {
    dimension1 match {
      case Some(x) => "[" + x._1 + ":" + x._2 +"]"
      case None => ""
    }
  }

  def genSecondDimensionCode = {
    dimension2 match {
      case Some(x) => "[" + x._1 + ":" + x._2 +"]"
      case None => ""
    }
  }

  def isArray = {
    dimension1.isDefined && dimension2.isDefined
  }
}

class DataDeclaration(dStructure: DataStructure, name: String, level: SecurityLevel) {
  //be very careful when modifying level
  def getName = name

  def getLevel = level

  def getDataStructure = dStructure

  def isFixed = level.isInstanceOf[Fixed]

  def genCode = {
    dStructure.genTypeCode + dStructure.genFirstDimensionCode + " " + name + dStructure.genSecondDimensionCode + ";\n" +
    dStructure.genTypeCode + " " + name + "_tag" +
      (if (dStructure.isArray) dStructure.genFirstDimensionCode else "") + ";\n"
  }
}

class Program(name: String, params: List[String], decl: List[DataDeclaration], defn: Definition) {

  def setCompilerInternals {
    Program.compilerInternals = new CompilerInternals(getRegisterTypeMapping, fallGraph, Map.empty[String, Int])
  }

  def dynamicCheckTransform = new Program(name, params, decl, defn.dynamicCheckTransform(getRegisterTypeMapping))

  def getRegisterTypeMapping: KindEnvironment = {
    val fixedRegs = decl.filter((x: DataDeclaration) => x.isFixed).foldLeft(Map[String, DataDeclaration]()) {
      (m, x) => m ++ Map(x.getName -> x)}
    val dynamicRegs = decl.filter((x: DataDeclaration) => !x.isFixed).foldLeft(Map[String, DataDeclaration]()) {
      (m, x) => m ++ Map(x.getName -> x)}
    val stateMap = defn.getStateMap
    val fixedStates = stateMap.filter((t) => t._2.isFixed)
    val dynamicStates = stateMap.filter((t) => !t._2.isFixed)
    new KindEnvironment(fixedRegs, dynamicRegs, fixedStates, dynamicStates)
  }

//  def assignmentSummary: Map[String, Set[String]] = {
//    //map from each statename to a tuple (1. set of registers assigned 2. set of other states dependent upon).
//    val summaryMapTuple = defn.assignmentSummary(name, Program.compilerInternals)
//    val cyclicGraph = summaryMapTuple.foldLeft(Map.empty[String, Set[String]]) {
//      (m, e) => m ++ Map(e._1 -> e._2._2)
//    }
//    val summaryMap = summaryMapTuple.foldLeft(Map.empty[String, Set[String]]) {
//      (m, e) => m ++ Map(e._1 -> e._2._1)
//    }
//    val tarjans = new TarjanAlgorithm(cyclicGraph)
//    tarjans.run(name, summaryMap)
//  }

  def fallGraph: Map[String, List[String]] = defn.fallGraph(name)

  def getFallConditionTags: Map[String, Set[Tag]] = defn.getFallConditionTags(name)

  def planarize: Map[String, List[(String, Command)]] = defn.planarize(List.empty[(String, Command)], name)

  private def wrapBlock(s: String, t: String) = {
    val instanceList = List(RegPosClk, RegNegClk, RegStar)
    "begin\n" +
      "if (reset == 1)\n" +
        "begin\n" +
        "cur_state <= 0;\n" + //initializations
        Program.compilerInternals.kindMapping.dynamicRegisters.values.filter((d) => {
          d.getDataStructure.dataType.isType(t) && (!d.getDataStructure.isArray)
        }).map((d) => {
          d.getName + "_tag <= 0;\n"
        }).mkString + //dynamic registers
        Program.compilerInternals.kindMapping.fixedRegisters.values.filter((d) => {
          d.getDataStructure.dataType.isType(t) && (!d.getDataStructure.isArray)
        }).map((d) => {
          d.getName + "_tag <= " + d.getLevel.genCode(Program.compilerInternals) + ";\n"
        }).mkString + //fixed registers
        Program.compilerInternals.kindMapping.dynamicStates.values.map((s) => {
          s.label + "_tag <= 0;\n"
        }).mkString + //dynamic states
        Program.compilerInternals.kindMapping.fixedStates.values.map((s) => {
          s.label + "_tag <= " + s.getLevel.genCode(Program.compilerInternals) + ";\n"
        }).mkString + //fixed states
        Program.compilerInternals.kindMapping.dynamicRegisters.values.filter((d) => {
          d.getDataStructure.dataType.isType(t) && d.getDataStructure.isArray
        }).map((d) => {
          "for (i=0; i<=" + d.getDataStructure.getMaxIndex + "; i=i+1)\n" +
          "begin\n" +
            d.getName + "_tag[i] <= 0;\n"
          "end\n"
        }).mkString + //dynamic array registers
        Program.compilerInternals.kindMapping.fixedRegisters.values.filter((d) => {
          d.getDataStructure.dataType.isType(t) && d.getDataStructure.isArray
        }).map((d) => {
          "for (i=0; i<=" + d.getDataStructure.getMaxIndex + "; i=i+1)\n" +
          "begin\n" +
            d.getName + "_tag[i] <= " + d.getLevel.genCode(Program.compilerInternals) + ";\n" +
          "end\n"
        }).mkString + //fixed array registers
        "end\n" +
      "end\n" +
      "else begin\n" +
        "case (cur_state)\n" +
           s +
        "endcase\n" +
      "end\n" + //end else
    "end\n"
  }

  private def stateLogicCode(cp: Map[String, String]) = {
    cp.foldLeft("") {
      (s, me) => {
        s + Program.compilerInternals.leafStateIndexMap(me._1) + ": begin\n" +
        me._2 +
        "end\n"
      }
    } + "default: ;\n"
  }

  def genCode: String = {
    val codePaths = planarize
    val leafStateIndexMap = (codePaths.keys zip Stream.from(0)).toMap
    Program.compilerInternals = new CompilerInternals(Program.compilerInternals.kindMapping,
                                              Program.compilerInternals.fallGraph,
                                              leafStateIndexMap)
    Program.compilerInternals.setCodeGenMode(Star())
    val starCode = codePaths.map((t) => {
      (t._1, t._2.map((tup) =>  {
        val state = tup._1
        val cmd = tup._2
        Program.compilerInternals.PCStack.clear()
        Program.compilerInternals.PCStack.push(StateOrRegisterReferenceTag(state))
        cmd.genCode(Program.compilerInternals)
      }).mkString)
    }) toMap

    Program.compilerInternals.setCodeGenMode(PosEdge())
    val posCode = codePaths.map((t) => {
      (t._1, t._2.map((tup) =>  {
        val state = tup._1
        val cmd = tup._2
        Program.compilerInternals.PCStack.clear()
        Program.compilerInternals.PCStack.push(StateOrRegisterReferenceTag(state))
        cmd.genCode(Program.compilerInternals)
      }).mkString)
    }) toMap


    Program.compilerInternals.setCodeGenMode(NegEdge())
    val negCode = codePaths.map((t) => {
      (t._1, t._2.map((tup) =>  {
        val state = tup._1
        val cmd = tup._2
        Program.compilerInternals.PCStack.clear()
        Program.compilerInternals.PCStack.push(StateOrRegisterReferenceTag(state))
        cmd.genCode(Program.compilerInternals)
      }).mkString)
    }) toMap


    val bitsForRepresentingStates = Util.bitsForRepresenting(leafStateIndexMap.size) - 1
    val curStateDimension = if (bitsForRepresentingStates > 0) "[" + bitsForRepresentingStates + ":0]" else ""

    //get all state names
    val stateNames = fallGraph.foldLeft(Set.empty[String]) {
      (s, t) => {
        s ++ t._2.toSet
      }
    }

    val stateTagRegDeclarations = stateNames.map((s) => "reg " + s + "_tag;").mkString("\n") + "\n"

    val stateTagWireDeclarations = stateNames.map((s) => "wire " + s + "_tag_wire;").mkString("\n") + "\n"

    val fallWireDecls = Program.compilerInternals.fallGraph.keys.map((s) => "wire " + s + "_fall;").mkString("\n") + "\n"

    val stateTagAssigns = Program.compilerInternals.fallGraph.keys.map((s) => {
      val children = Program.compilerInternals.fallGraph(s)
      children.map((c) => "assign " + c + "_tag_wire = " + s + "_fall | " + c + "_tag;\n" ).mkString
    }).mkString

    val fallConditionTags = getFallConditionTags

    val fallWireAssigns = (fallConditionTags - name).keys.map((s) => {
      "assign " + s + "_fall = " + s + "_tag_wire | " +
        fallConditionTags(s).map(_.genCode(Program.compilerInternals)).mkString(" | ") + ";\n"
    }).mkString + "assign " + name + "_fall = 0;\n"

    "module " + name + "(" + (params ++ List("clk", "reset")).mkString(",") + ");\n" +
    "input clk; \n" +
    "input reset; \n" +
    "reg" + curStateDimension + " cur_state;\n" +
    decl.map((x: DataDeclaration) => x.genCode).mkString +
    stateTagRegDeclarations +
    stateTagWireDeclarations +
    fallWireDecls +
    "integer i;\n" +
    stateTagAssigns +
    fallWireAssigns +
    "\nalways @ (posedge clk or posedge reset)\n" +
    wrapBlock(stateLogicCode(posCode), "pos")  +
    "\nalways @ (negedge clk or posedge reset)\n" +
    wrapBlock(stateLogicCode(negCode), "neg") +
    "always @ (*)\nbegin\n" +
    wrapBlock(stateLogicCode(starCode), "star") +
    "endmodule"
  }
}

object Program {
  var compilerInternals: CompilerInternals = null
}

class InvalidProgramException(msg: String) extends Exception{
  def message = msg
}

class StateNode(name: String, children: Option[List[StateNode]], params: List[String]) {
  def getName = name

  def getParams = params

  def getChildren = children
}

class CaissonCompilerException(msg: String) extends Exception {
  def message: String = msg
}

class ValidationException(msg: String) extends Exception {
  def message: String = msg
}

sealed abstract class Tag extends Expr {
  def getTags: Set[Tag]
}

case class ConcreteTag(value: String) extends Tag {
  value match { //TODO: extend to handle any <specified> lattice
    case "H" => ; //safe
    case "L" => ; //safe
    case _ => throw new CaissonParseException("Illegal tag: " + value)
  } //this code is executed when THIS is constructed

  override def genCode(ci: CompilerInternals) = {
    value match {
      case "H" => "1"
      case "L" => "0"
      case _ => throw new CaissonCompilerException("Illegal tag: " + value + " generated by compiler")
    }
  }

  override def getTags = Set(this)
}

case class PC() extends Tag {
  override def genCode(ci: CompilerInternals) = {
    ci.PCStack.top.genCode(ci)
  }

  override def getTags = Set.empty[Tag]
}

case class StateOrRegisterReferenceTag(name: String) extends Tag {
  override def genCode(ci: CompilerInternals) = {
    name + "_tag"
  }

  override def getTags = Set(this)
}

case class RegisterArrayReferenceTag(registerExpression: ArrayExpr) extends Tag {
  override def genCode(ci: CompilerInternals) = {
    registerExpression.genTagCode(ci)
  }

  override def getTags = Set(this)
}

sealed abstract class SecurityLevel {
  def genCode(ci: CompilerInternals): String
}

case class Fixed(level: ConcreteTag) extends SecurityLevel {
  override def genCode(ci: CompilerInternals) = level.genCode(ci)
}

case class Dynamic(var level: ConcreteTag) extends SecurityLevel {
  override def genCode(ci: CompilerInternals) = level.genCode(ci)
}

//this is used in the dynamic checking transformed AST
sealed abstract class TagExpressions extends Tag

case class JoinTag(elements: Set[Tag]) extends TagExpressions {
  override def genCode(ci: CompilerInternals) = {
    elements.map((e) => e.genCode(ci)).mkString(" | ")
  }

  override def getTags = elements
}

case class LessThanTag(left: Tag, right: Tag) extends TagExpressions {
  override def genCode(ci: CompilerInternals) = {
    left.genCode(ci) + " <= " + right.genCode(ci)
  }

  override def getTags = Set(left, right)
}

case class GreaterThanTag(left: Tag, right: Tag) extends TagExpressions {
  override def genCode(ci: CompilerInternals) = {
    left.genCode(ci) + " >= " + right.genCode(ci)
  }

  override def getTags = Set(left, right)
}
