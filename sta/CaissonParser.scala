/*
  Please refer to licensing information in LICENSE.txt
  Author: Vineeth Kashyap
  Email: vineeth@cs.ucsb.edu
  In this file, the parser-combinator for Caisson is specified.
*/
package sta;

import scala.util.parsing.combinator._

class CaissonParser extends VerilogParser {  
    def program: Parser[Program] = "prog"~>ident~"("~id_list~")"~"="~rep1(decl)~rep(parameter)~"in"~defn~rep(assign)~rep(instance)~reset ^^ 
    	{case name~"("~params~")"~"="~decl~parameters~"in"~defn~assigns~instances~reset => new Program(name, params, decl, new StateDefinition(name, "L", List(), None, defn._1, defn._2), parameters, assigns, instances, reset)}     
        
    override def single_dec : Parser[SingleDec] = ident~opt(dim)~":"~ident ^^ { case id~dim~_~t => new SingleDec(id, dim, t)}
    																
    def defn : Parser[(Option[List[StateDefinition]], StatementList)] = opt("let"~>rep1(stateDefinition)<~"in")~rep(stmt) ^^ {case sd~st => (sd, new StatementList(st))}
        
    def stateDefinition: Parser[StateDefinition] = "state"~>pair(":")~"("~repsep(pair(":"),",")~")"~opt(constraintList)~"="~"{"~defn<~"}" ^^ 
    	{ case idtype~_~vmap~_~clist~_~_~defs => new StateDefinition(idtype._1, idtype._2, vmap, clist, defs._1, defs._2)}                                       								

    def pair(sep : String) : Parser[(String, String)] = ident~sep~ident ^^ {case id~_~t => (id,t)}
    
    def constraintList: Parser[List[(String,String)]] = "["~>repsep(pair("<"),",")<~"]"
        
    override def stmt: Parser[Statement] = nonblockAssign | conditional | cases | jump | fall
    
    def fall: Parser[Fall] = "fall"~";" ^^^ (Fall())
        
    def jump: Parser[Jump] =  "goto"~>ident~"("~repsep(ident, ",")<~")"~";" ^^ { case target~"("~varList => Jump(target, varList) }
    
    def reset: Parser[StatementList] = "reset"~"{"~>rep(stmt)<~"}" ^^ (StatementList)
}
