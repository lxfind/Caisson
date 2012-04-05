package verilog;

class Environment(val isStatic : Boolean, val isMain : Boolean, val allModuleNames : List[String], val symbolTable : Map[String, DataType], var clkAssignSet : Set[String])

object Store {
  var vectors : Map[String, Int] = Map()
  var init : StatementList = new StatementList(List())
  var params : List[String] = List()
}

class Task[T](val emptyValue : T, val mergeFunction : (T,T) => T)
object GetAssignVarSet extends Task[Set[String]](Set(), (a,b) => a++b)