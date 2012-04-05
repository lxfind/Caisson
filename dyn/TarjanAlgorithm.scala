
/**
  Please refer to licensing information in LICENSE.txt
  Author: Vineeth Kashyap
  Email: vineeth@cs.ucsb.edu
  This file contains the implementation of Tarjan's algorithm.
*/
package dyn

import scala.collection.mutable
import scala.math

class TarjanAlgorithm(graph: Map[String, Set[String]]) {
  val visited = mutable.Map.empty[String, Boolean]
  graph.keys.foreach((n: String) => visited += (n -> false))
  val root = mutable.Map.empty[String, String]
  val inComponent = mutable.Map.empty[String, Boolean]
  graph.keys.foreach((n: String) => inComponent += (n -> false))
  val stack = new mutable.Stack[String]
  var counter = 0
  val id = mutable.Map.empty[String, Int]

  def getNextID:Int = {
    counter += 1
    counter
  }

  def visit(v: String) {
    visited(v) = true
    id(v) = getNextID
    root(v) = v
    inComponent(v) = false
    stack.push(v)
    graph(v).foreach((w: String) => {
      if (!visited(w)) visit(w)
      if (!inComponent(w)) root(v) = min(root(v), root(w))
    })
    if (root(v) == v) {
      var w = v
      do {
        w = stack.pop
        inComponent(w) = true
      } while(w != v)
    }
  }

  def min(a: String, b: String): String = {
    if(id(a) < id(b)) a else b
  }

  def run(start: String, originalSummaryMap: Map[String, Set[String]]): Map[String, Set[String]] = {
    visit(start)
    val rootMap = mutable.Map.empty[String, Set[String]]
    //setup rootMap
    for(k <- root.keys) {
      val v = root(k)
      if (rootMap.contains(v))
        rootMap(v) += k
      else
        rootMap(v) = Set(k)
    }
    rootMap.toMap
    val dac = mutable.Map.empty[String, Set[String]]
    for (k <- rootMap.keys) {
      val v = rootMap(k)
        //find all outputs mapped to roots, remove myself from it
        dac(k) = v.foldLeft(Set.empty[String])((s, n) => s ++ graph(n).map(root(_))) -- Set(k)
    }
    val summaryMap = mutable.Map.empty[String, Set[String]]
    //calculate summary recursively, also set the summaries of other master nodes
    def calcSummary(s: String): Set[String] = {
      summaryMap(s) = rootMap(s).foldLeft(Set.empty[String]) {
        (ac, state) => ac ++ originalSummaryMap(state)
      } ++ dac(s).foldLeft(Set.empty[String]) {
        (ac, state) => ac ++ calcSummary(state)
      }
      summaryMap(s)
    }
    calcSummary(start)
    for(k <- rootMap.keys) {
      val v = rootMap(k)
      v.foreach((state) => summaryMap(state) = summaryMap(k))
    }
    summaryMap.toMap
  }
}

/* object Runner extends App {
  val g = Map("root" -> Set("master", "group"),
              "master" -> Set("group"),
              "group" -> Set("master", "S1", "S2"),
              "S1" -> Set("S2"),
              "S2" -> Set("S1"))
  val m = Map("root" -> Set("a"),
  "master" -> Set("b"),
  "group" -> Set("c"),
  "S1" -> Set("d"),
  "S2" -> Set("e"))

  val a = new TarjanAlgorithm(g)
  println(a.run("root", m))
} */