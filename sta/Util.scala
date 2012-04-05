/*
  Please refer to licensing information in LICENSE.txt
  Author: Vineeth Kashyap
  Email: vineeth@cs.ucsb.edu
  This file has some utility functions.
*/
package sta;

object Util {  
  def substituteConstraints(cl: List[(SimpleType, SimpleType)], subs: Map[String, SimpleType]): List[(SimpleType, SimpleType)] = {
    cl.map(e => (substituteType(e._1, subs), substituteType(e._2, subs)))
  }

  def substituteType(t: SimpleType, m: Map[String, SimpleType]): SimpleType = {
    if (m.contains(t.level)) m(t.level)
    else t
  }
  
  def bottomStateType = new StateType(SimpleType("L"), List[SimpleType](), List[(SimpleType, SimpleType)]())    
  
  def computeKappa(tm: Map[String, CaissonType]): DirectedLatticeGraph = {
    val constraints = tm.values.filter(_.isInstanceOf[StateType]).map(_.asInstanceOf[StateType].constraints).reduceLeft((a, b) => a ++ b)
    val kappa = new DirectedLatticeGraph()
    constraints.foreach(c => kappa.addEdge(c._1.level, c._2.level))
    if (kappa.isConsistent) kappa
    else throw new CaissonTypeException("Inconsistent type constraints specification")
  }

  def bitsForRepresenting(x: Int) : Int = if (x>1) math.round(math.ceil(math.log(x)/math.log(2))).toInt else 1
  
  def dimGen(x : Int) : Option[Dim] = {
    val bits = bitsForRepresenting(x)
    (if (bits>1) Some(new DoubleDim(Number((bits-1).toString), Number("0"))) else None)
  } 
  
  def ternaryGen(cond : String, values : List[String]) = {
	  values.indices.tail.foldLeft[Expression](Variable(values.first, true))((t, i) => new TernaryExpression(cond, i, values(i), t))
	}
}
