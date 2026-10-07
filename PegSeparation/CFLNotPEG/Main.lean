import PegSeparation.CFLNotPEG.Assembly
import PegSeparation.CFLNotPEG.External.LoffForwardRepaired
import PegSeparation.CFLNotPEG.External.Ko2026
import PegSeparation.CFLNotPEG.Reduction.GenericTransfer
import PegSeparation.CFLNotPEG.Witness.DirectPEGPositive

set_option linter.style.header false


namespace PegSeparation.CFLNotPEG

theorem loffForwardRepaired : PegSeparation.LoffForwardStatement :=
  PegSeparation.External.LoffForwardRepaired.loffForwardStatement

theorem ko2026MultiphaseIPLowerBound :
    PegSeparation.Ko2026MultiphaseIPLowerBoundStatement :=
  PegSeparation.External.Ko2026.multiphaseIPLowerBound

def assumptions : PegSeparation.ExternalAssumptions where
  loffForward := loffForwardRepaired
  ko2026MultiphaseIPLowerBound := ko2026MultiphaseIPLowerBound

theorem finalSeparation :
    Language.IsContextFree PegSeparation.CFLNotPEG.WitnessLanguage ∧
      ¬ PegSeparation.CFLNotPEG.RecognizedByTotalPEG
        PegSeparation.CFLNotPEG.WitnessLanguage :=
  PegSeparation.CFLNotPEG.final_separation assumptions

end PegSeparation.CFLNotPEG

#check PegSeparation.CFLNotPEG.finalSeparation

#print axioms PegSeparation.CFLNotPEG.concreteC_isContextFree
#print axioms PegSeparation.CFLNotPEG.witnessLanguage_isContextFree
#print axioms PegSeparation.CFLNotPEG.totalPEG_for_witness_implies_SCA_for_C
#print axioms PegSeparation.CFLNotPEG.hardWord_mem_C_iff_answer
#print axioms PegSeparation.CFLNotPEG.scaToDynamicCompiler
#print axioms PegSeparation.CFLNotPEG.fastMultiphaseIP_of_SCA
#print axioms PegSeparation.CFLNotPEG.multiphaseIPLowerBound
#print axioms PegSeparation.CFLNotPEG.C_not_SCA
#print axioms PegSeparation.CFLNotPEG.final_separation
#print axioms PegSeparation.CFLNotPEG.final_separation_from_internal_pipeline

#print axioms PegSeparation.CFLNotPEG.loffForwardRepaired
#print axioms PegSeparation.External.Ko2026.multiphaseIPLowerBound
#print axioms PegSeparation.CFLNotPEG.ko2026MultiphaseIPLowerBound
#print axioms PegSeparation.CFLNotPEG.assumptions
#print axioms PegSeparation.CFLNotPEG.finalSeparation

#print axioms PegSeparation.Witness.DirectPEG.grammar_isLoffTotal
#print axioms PegSeparation.Witness.DirectPEG.grammar_recognizes_iff_C
#print axioms PegSeparation.Witness.DirectPEG.C_recognizedByTotalPEG

#print axioms PegSeparation.Reduction.GenericTransfer.exactTransferAtDimension
#print axioms PegSeparation.Reduction.GenericTransfer.transferAtDimension
#print axioms PegSeparation.Reduction.GenericTransfer.genericTransferTheorem
