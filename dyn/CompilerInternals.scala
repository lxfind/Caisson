package dyn

class CompilerInternals(kmap: KindEnvironment,
                        fg: Map[String, List[String]],
                        lIndexMap: Map[String, Int]) {
  val PCStack = scala.collection.mutable.Stack[Tag]()
  PCStack.push(ConcreteTag("L"))

  var cdGnMode: CodeGenMode = Star()

  def kindMapping = kmap

  def fallGraph = fg

  def setCodeGenMode(newMode: CodeGenMode) {
    cdGnMode = newMode
  }

  def codeGenMode = cdGnMode

  def leafStateIndexMap = lIndexMap

  def gotoStateIndexMap = fallGraph.mapValues((ls) => {
    var firstChild = ls(0)
    while (fallGraph.contains(firstChild)) firstChild = fallGraph(firstChild)(0)
    lIndexMap(firstChild)
  }) ++ lIndexMap
}

sealed abstract class CodeGenMode
case class Star() extends CodeGenMode
case class PosEdge() extends CodeGenMode
case class NegEdge() extends CodeGenMode