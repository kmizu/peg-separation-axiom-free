import PegSeparation.Closure.GreibachProofMain
import PegSeparation.Closure.InverseImageNonerasing
import PegSeparation.CFLNotPEG.InternalLowerBoundMain
import PegSeparation.CFLNotPEG.Main

/-!
# Greibach's hardest language has no total PEG — with only the standard axioms

`fullyInternalSeparation`: the artifact's witness `C^R` is context-free and has no total PEG, with both external
statements (the PEG–SCA characterization and the multiphase lower bound) discharged by the artifact's own proofs.

`greibachHardest_not_totalPEG_noAxioms`: Greibach's hardest language is context-free and has no total PEG. If it
had one, so would it without `ε`, and so would every context-free language — the witness among them — as an inverse
image under a nonerasing homomorphism (`greibachWitness_nonerasing`, `recognizedByTotalPEG_inverseImage_nonerasing`).
-/

namespace PegSeparation.CFLNotPEG

theorem fullyInternalSeparation :
    Language.IsContextFree WitnessLanguage ∧ ¬ RecognizedByTotalPEG WitnessLanguage :=
  final_separation_from_internal_pipeline
    ⟨loffForwardRepaired, internalMultiphaseIPLowerBound⟩ internalMultiphaseIPLowerBound

end PegSeparation.CFLNotPEG

namespace PegSeparation.Closure.GreibachHardest

open PegSeparation
open PegSeparation.Closure.GreibachProof

/-- **Greibach's hardest language is context-free and has no total PEG.** -/
theorem greibachHardest_not_totalPEG_noAxioms :
    greibachWitness.language.IsContextFree ∧ ¬ greibachWitness.IsTotalPEG := by
  refine ⟨greibachWitness.isContextFree, fun hL => ?_⟩
  letI : Fintype greibachWitness.HardAlphabet := greibachWitness.hardAlphabetFintype
  letI : DecidableEq greibachWitness.HardAlphabet := greibachWitness.hardAlphabetDecidableEq
  have hL' : RecognizedByTotalPEG greibachWitness.language := hL
  have hL1 := recognizedByTotalPEG_sub_epsilon hL'
  obtain ⟨hom, hne, hcase⟩ := greibachWitness_nonerasing CFLNotPEG.ConcreteAlphabet inferInstance inferInstance
    CFLNotPEG.WitnessLanguage CFLNotPEG.fullyInternalSeparation.1
  apply CFLNotPEG.fullyInternalSeparation.2
  rcases hcase with h | h
  · rw [h]; exact recognizedByTotalPEG_inverseImage_nonerasing hom hne hL'
  · rw [h]; exact recognizedByTotalPEG_inverseImage_nonerasing hom hne hL1

end PegSeparation.Closure.GreibachHardest

#print axioms PegSeparation.CFLNotPEG.fullyInternalSeparation
#print axioms PegSeparation.Closure.GreibachHardest.greibachHardest_not_totalPEG_noAxioms
