/*
  Please refer to licensing information in LICENSE.txt
  Author: Vineeth Kashyap, Xun Li
  Email: vineeth@cs.ucsb.edu, xun@cs.ucsb.edu
  This is the main file for executing the compiler.
*/
package sta;

import java.io.FileReader

object CaissonCompiler {
    def main(args: Array[String]) {              
       try {
         val (inputDir, outputDir, files) = parseArguments(args) //parse arguments and get file names
                  
         files.foreach((f:String) => {
           println("Compiling file " + f + "...");
           //Parsing
           val reader = new FileReader(inputDir + "/" + f)
           val parser = new CaissonParser()
           val ast = parser.parseAll(parser.program, reader) match {
           	case parser.Success(p, _) => p //successful parsing, gets the AST
           	case fail => throw new Exception("In file " + f + ":\n" + fail);
           }
           reader.close();   
           
           //Validate
           validate(ast);
           
           //Build the environment
           val env = ast.computeEnvironment(f.equals(files(0)))
           
           //Type Check here
           val typeMap : Map[String, CaissonType] = env.symbolTable.map(x => (x._1->SimpleType(x._2.level)))++env.stateTable.map(x => (x._1->x._2.sectype))
           val kappa = Util.computeKappa(typeMap)
           ast.caissonType(env, kappa)
             
           //Code Generation
           val writer = new java.io.FileWriter(outputDir + "/" + getOutputName(f))
           writer.write(ast.codeGen(env)) // generate code and write it to the output file, which is by default "a.v"          
           writer.close()    
         })
                    
         System.out.println("Compilation finished");
         
       } catch {                             
          case e: Exception => e.printStackTrace()
       }
    }       

    def validate(ast: Program) {
      /*
       Validate the following assumptions on the Program:
              1. All the variables and type variable have distinct names
              2. A default child state cannot take any parameters
              3. Either both the branches of an if command must execute a goto or fall, or neither of them do.
              4. All paths through a state end in either a goto or a fall
              5. A leaf state cannot contain a fall
              6. Every goto targets a defined label, and can only target a state in the same group and at the same nested depth
       */
      ast.p(DupNameCheck)
      ast.p(DefaultChildNoParamCheck)
      ast.p(BranchGotoFallCheck)
      ast.p(EndWithGotoFallCheck)
      ast.p(LeafNoFallCheck)
      ast.p(GotoSameLevelCheck)     
    }

    private def printHelpAndExit(): (String, String, List[String]) = {
      println("Usage: CaissonCompiler [InputDir] [OutputDir] [Files]")
      exit(-1)
    }

    //Parse command line arguments
    // Return: InputDir, OutputDir, FileNames
    private def parseArguments(args: Array[String]): (String, String, List[String]) = {
      (if (args.size>=3) ((args(0), args(1), args.tail.tail.toList)) else printHelpAndExit)           
    }
    
    //Given an input file x.caisson, output file name will be x.v
    private def getOutputName(inputName: String) = {
      val index = inputName.findLastIndexOf(_=='.') 
      if (index>=0) (inputName.substring(0,index) + ".v") else (inputName + ".v")     
    }
}