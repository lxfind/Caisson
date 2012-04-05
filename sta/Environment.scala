/*
  Please refer to licensing information in LICENSE.txt
  Author: Vineeth Kashyap
  Email: vineeth@cs.ucsb.edu
  This file describes the environment that is passed around for type checking.
*/

//pm : Map from modulename to the list of (map from module parameter name to its datatype and security level)
/*class Environment(tm: Map[String, CaissonType], sm: Map[String,State], pm: Map[String,Map[String,(DataType, String)]], im: Boolean) {
  //var isMain : Boolean = true
  var dataTypeMap: Map[String,DataType] = Map()
  def this(tm : Map[String, CaissonType]) = this(tm, Map[String,State](), Map[String,Map[String,(DataType, String)]](), true)
  def typeMap: Map[String, CaissonType]  = tm
  def states: Map[String,State] = sm
  def portMap = pm
  //def getIsMain = isMain
  def isMain : Boolean = im
  def + (that: Environment): Environment = new Environment(tm ++ that.typeMap, sm, pm ++ that.portMap, true)
  def ++ (that : Map[String,Map[String,(DataType, String)]]) = new Environment(tm, sm, pm ++ that, true)
  def +++ (that: Map[String,State]) = new Environment(tm, that, pm, true)
  
  override def toString = tm.toString
}*/

// Vector Map: Map from each Vector Expresion to a triple(IsRead, Temp Variable Name, Data Width) 
package sta;

class Environment(val symbolTable : Map[String, SymbolInfo], val stateTable : Map[String, StateInfo], val assignSet : Set[String], val readSet : Set[String], val isMain : Boolean) {
       
  // Return the list of states who has been gotoed from other states with parameters  
  def getGotoStates : List[StateInfo] = stateTable.values.toList.filter(_.gotoNum>1)
  
  // (Pins, declarations, reset code, clk code, star code) for state machine related variables
  private def getExtraForSM = {
    val params = getGotoStates.map(x => ("cond_"+x.name, x.gotoNum))++List(("cur_state", stateTable.filter(_._2.isLeaf).size))
    if (isMain) (List(), 
    			params.flatMap(x => List(new Declaration(Register, x._1, x._2), new Declaration(Register, x._1+"_w", x._2))),
    			params.map(_._1 + " <= 0;\n").mkString,
    			params.map(x => x._1 + " <= " + x._1 + "_w;\n").mkString,
    			params.map(x => x._1 + "_w <= " + x._1 + ";\n").mkString)
    else		(params.map(_._1), params.map(x => new Declaration(Input, x._1, x._2)), "", "", "")    
  }
  
  // Get extra (declarations, assigns, star code, clk code) for parameterized variables
  private def getExtraForVar = {
    val symbols = symbolTable.filter(_._2.isParam)
    symbols.map(x => if (x._2.isVector) (List(), List(), "", "") else {
      val name = x._1
      val s = x._2
      val wire = name + "_w"
      val cond = "cond_" + s.ownerState
      val rSet = (List(new Declaration(Wire, name, s)), List(Assign(Variable(name, true), Util.ternaryGen(cond, s.realNames))))       			 
      val wSet = if (assignSet.contains(name)) (List(new Declaration(Register, wire, s)), 
    		  									(if (s.datatype.equals(Register)) List() else s.realNames.indices.map(i => new Assign(s.realNames(i), cond, i, wire))),
    		  									(if (s.datatype.equals(Register)) wire + " <= " + name + ";\n" else wire + " <= 0;\n"),
    		  									(if (s.datatype.equals(Register)) s.realNames.indices.map(i => s.realNames(i) + " <= " + cond + "==" + i + "?" + wire + ":" + s.realNames(i) + ";\n").mkString else ""))
    		  	 else (List(), List(), "", "")
      (rSet._1++wSet._1, rSet._2++wSet._2, wSet._3, wSet._4)
    }).reduce((a,b) => (a._1++b._1, a._2++b._2, a._3+b._3, a._4+b._4))
  }
  
  // Get vector initializations for several modules
  private def getExtraReset:(String,List[Declaration]) = {
    val i = List(new Declaration(Integer, "i"));
    if (this.stateTable.contains("reg_file"))
      ("for(i=0; i < 32; i = i + 1) begin if(i == 29) begin registers_h[i] <= 32'h80000000; registers_l[i] <= 32'h80000000; end else begin registers_h[i] <= 0; registers_l[i] <= 0; end end\n", i)
    else if (this.stateTable.contains("small_cache"))
      ("for(i = 0; i < CACHE_SIZE; i = i + 1) begin cache_l[i] <= 0; cache_h[i] <= 0; end\n", i)
    else if (this.stateTable.contains("mem_array"))
      ("$readmemh(\"../../../Processors/BaseFullProcessor/tests/rss\", mem_l, 'h0);\n" + 
      "case (testbenchID)\n" +
    	     "0: $readmemh(\"../../../Processors/BaseFullProcessor/tests/bubblesort/vsim\", mem_l, 'h2400000);\n"+
          "1: $readmemh(\"../../../Processors/BaseFullProcessor/tests/mm/vsim\", mem_l, 'h2400000);\n"+
          "2: $readmemh(\"../../../Processors/BaseFullProcessor/tests/aes/vsim\", mem_l, 'h2400000);\n"+
	        "3: $readmemh(\"../../../Processors/BaseFullProcessor/tests/divider_test/vsim\", mem_l, 'h2400000);\n"+
	        "4: $readmemh(\"../../../Processors/BaseFullProcessor/tests/specrand/vsim\", mem_l, 'h2400000);\n"+
	        "5: $readmemh(\"../../../Processors/BaseFullProcessor/tests/mcf/vsim\", mem_l, 'h2400000);\n"+
	        "6: $readmemh(\"../../../Processors/BaseFullProcessor/tests/bzip2/vsim\", mem_l, 'h2400000);\n"+
				  "7: $readmemh(\"../../../Processors/BaseFullProcessor/tests/singlefputest/vsim\", mem_l, 'h2400000);\n"+
				  "8: $readmemh(\"../../../Processors/BaseFullProcessor/tests/fft/vsim\", mem_l, 'h2400000);\n"+
				  "9: $readmemh(\"../../../Processors/BaseFullProcessor/tests/sha/vsim\", mem_l, 'h2400000);\n"+
          "10:$readmemh(\"../../../Processors/BaseFullProcessor/tests/rijndael/vsim\", mem_l, 'h2400000);\n"+
	      "endcase\n",i)
	else ("",List())	
  }
  
  //Get extra (module pins, declarations, assigns, reset code, clk code, star code)    
  def getExtra : (List[String], List[Declaration], List[Assign], String, String, String) = {
    val extraSM = getExtraForSM
    val extraVar = getExtraForVar
    val extraReset = getExtraReset
    (extraSM._1, extraSM._2++extraVar._1++extraReset._2, extraVar._2, extraSM._3+extraReset._1, extraSM._4+extraVar._4, extraSM._5+extraVar._3)
  } 
  
  def typeMap(name : String) = if (this.symbolTable.contains(name)) SimpleType(this.symbolTable(name).level) else stateTable(name).sectype
}

//isParam: whether this symbol is a parameterized variable
class SymbolInfo(val datatype : DataType, val dim1 : Option[Dim], val dim2 : Option[Dim], val level : String, val isSigned : Boolean, val isParam : Boolean, val realNames : List[String], val ownerState : String) {
  def this(datatype : DataType, dim1 : Option[Dim], dim2 : Option[Dim], level : String, isSigned : Boolean) = this(datatype, dim1, dim2, level, isSigned, false, List(), "")
  def this() = this(null, None, None, "L", false, false, List(), "")
  def isArray = dim1.isDefined
  def isVector = dim2.isDefined
}

class StateInfo(val name : String, val sectype : StateType, val args : List[(String, String)], val isLeaf : Boolean, val id : Int, val gotoNum : Int, val fall : Fall, val children : List[String])

/*
 * Task contains two members: emptyValue represents the empty return value, and mergeFunction tells how to merge two return results.
 * Here is the description of all tasks:
 * Information collecting tasks:
 * 1. GetAssignVarSet: get all variables that gets written in the program
 * 2. GetReadVarSet: get all variables that gets read in the program (ends up not been used, can be removed)
 * 3. GetVectors: get all vectors in the code (ends up not been used, can be removed)
 * 4. GetGotos: get all gotos with their argument lists
 * 5. GetFall: get the fall statement in the current state (should be unique)
 * 
 * Validation tasks: (their descriptin can be found in the method "validate" of CaissonCompiler.scala
 * DefaultChildNoParamCheck,  BranchGotoFallCheck, EndWithGotoFallCheck, LeafNoFallCheck, GotoSameLevelCheck
 */
class Task[T](val emptyValue : T, val mergeFunction : (T,T) => T)
object GetAssignVarSet extends Task[Set[String]](Set(), (a,b) => a++b)
object GetReadVarSet extends Task[Set[String]](Set(), (a,b) => a++b) 
object GetVectors extends Task[List[(Boolean, Expression, Int)]](List(), (a,b) => a++b)
object GetGotos extends Task[List[(String, List[String])]](List(), (a,b) => a++b)
object GetFall extends Task[Fall](null, (a,b) => if (a==null) b else if (b==null) a else throw new Exception("Sorry but only one fall is allowed in a state"))

object DupNameCheck extends Task[(Set[String],Set[String])]((Set(), Set()), (a,b) => {
  val vars = (if (a._1.intersect(b._1).isEmpty) a._1++b._1 else throw new Exception("Duplicated declaration of variable:"+a._1.intersect(b._1)))
  val types = a._2++b._2
  if (vars.intersect(types).isEmpty) (vars,types) else throw new Exception("Duplicated declaration of variable and type:"+vars.intersect(types))
}) 
object DefaultChildNoParamCheck extends Task[Int](0, (_,_)=>0)
object BranchGotoFallCheck extends Task[Boolean](false, (a,b) => a|b)
object EndWithGotoFallCheck extends Task[Boolean](false, (a,b) => if (b) b else false)
object LeafNoFallCheck extends Task[Boolean](false, (a,b) => a|b)
object GotoSameLevelCheck extends Task[(Boolean,List[String])]((true,List()), (a,b) => if (b._1) (true,a._2++b._2) else (true, b._2)) 