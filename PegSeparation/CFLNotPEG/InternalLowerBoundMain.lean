import PegSeparation.CFLNotPEG.External.LarsenYuBetaOneInternal
import PegSeparation.CFLNotPEG.LowerBound.MultiphaseLowerBound

set_option linter.style.header false


namespace PegSeparation.CFLNotPEG

theorem internalLarsenYuBetaOneExactCost :
    PegSeparation.LarsenYuBetaOneExactStatement :=
  PegSeparation.External.LarsenYuBetaOneInternal.larsenYuBetaOneInternal

def internalLowerBoundAssumptions :
    PegSeparation.InternalLowerBoundAssumptions where
  larsenYuBetaOne := internalLarsenYuBetaOneExactCost

theorem internalMultiphaseIPLowerBound :
    PegSeparation.Ko2026MultiphaseIPLowerBoundStatement :=
  PegSeparation.LowerBound.MultiphaseLowerBound.not_hasFastMultiphaseIPFamily
    internalLowerBoundAssumptions

end PegSeparation.CFLNotPEG

#check PegSeparation.CFLNotPEG.internalMultiphaseIPLowerBound

#print axioms PegSeparation.CFLNotPEG.internalLarsenYuBetaOneExactCost
#print axioms PegSeparation.CFLNotPEG.internalLowerBoundAssumptions
#print axioms PegSeparation.CFLNotPEG.internalMultiphaseIPLowerBound
