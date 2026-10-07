import PegSeparation.CFLNotPEG.Assembly
import PegSeparation.CFLNotPEG.InternalLowerBoundMain
import PegSeparation.CFLNotPEG.Main

namespace PegSeparation.CFLNotPEG

/-- The separation with both external statements discharged by the artifact's own proofs. -/
theorem fullyInternalSeparation :
    Language.IsContextFree WitnessLanguage ∧ ¬ RecognizedByTotalPEG WitnessLanguage :=
  final_separation_from_internal_pipeline
    ⟨loffForwardRepaired, internalMultiphaseIPLowerBound⟩ internalMultiphaseIPLowerBound

end PegSeparation.CFLNotPEG

#print axioms PegSeparation.CFLNotPEG.fullyInternalSeparation
