
/*
  Please refer to licensing information in LICENSE.txt
  Author: Vineeth Kashyap
  Email: vineeth@cs.ucsb.edu
  This file describes register type environments
*/
package dyn

class KindEnvironment(fRs: Map[String, DataDeclaration],
                      dRs: Map[String, DataDeclaration],
                      fSs: Map[String, StateDefinition],
                      dSs: Map[String, StateDefinition]) {
  def fixedRegisters = fRs

  def dynamicRegisters = dRs

  def fixedStates = fSs

  def dynamicStates = dSs
}