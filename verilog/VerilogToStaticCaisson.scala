package verilog;

import java.io.FileReader

object VerilogToStaticCaisson {

  def main(args: Array[String]): Unit = {
    try {
    	val (isStatic, inputpath, outputpath, files) = parseArguments(args);
    	val allModuleNames = files.map(getAbsName(_))
    	
    	val parser = new VerilogParser();    	
    	files.foreach((filename:String) => {
    	  println("Compiling " + filename + "...")
    	  Store.init = new StatementList(List())
    	  val reader = new FileReader(inputpath + "/" + filename)         
          val AST = parser.parseAll(parser.module, reader) match {
            case parser.Success(p, _) => p //successful parsing, gets the AST          
            case f => throw new Exception("In file "+filename+":\n"+f);
          }
          reader.close()
                    
          //Semantic Check
          val name = getAbsName(filename)
          AST.semCheck(name)
          
          if (!name.equals(AST.name)) throw new Exception("File name should be identical to module name: "+filename + " vs. "+AST.name)
          
          val writer = new java.io.FileWriter(outputpath + "/" + name + (if (isStatic) ".caisson" else ".dcaisson"))
          val env = new Environment(isStatic, filename==files(0), allModuleNames, AST.symbols, AST.p(GetAssignVarSet))
          writer.write(AST.patch(env).codeGen(env))
          writer.close()
    	})
    	
    	println("Parsing finished.")
    } catch {
      case e : Exception => e.printStackTrace()
    }
    
  }
  
  private def parseArguments(args: Array[String]) : (Boolean, String, String, List[String]) =
    (if (args.size>=4)
      ((args(0) match {
      	case "-static" => true
      	case "-dynamic" => false
      	case _ => {usageAndExit; true}}), 
      args(1), args(2), args.tail.tail.tail.toList)
      else { usageAndExit }
    )
    
  private def usageAndExit : (Boolean, String, String, List[String]) = {
    println("Usage: scala VerilogToCaisson [-staic | -dynamic] [input path] [output path] [files]"); 
    exit(1);
  }
  
  //Get absolute name without extension
  private def getAbsName(filename : String) = {
    val index = filename.findLastIndexOf(_=='.')
    (if (index<=0) throw new Exception("File" + filename +" does not have extensions. (Verilog files should have .v extension)") else filename.substring(0,index))
  }

}