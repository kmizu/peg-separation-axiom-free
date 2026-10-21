import PegSeparation.Closure.GreibachProofMain
import PegSeparation.Closure.InverseImageNonerasing
import PegSeparation.CFLNotPEG.InternalLowerBoundMain
import PegSeparation.CFLNotPEG.Main
import PegSeparation.Closure.PartialPEGTotalMain
import PegSeparation.Closure.PartialPEGBridge

/-!
# Greibach's hardest language has no total PEG — with only the standard axioms

`fullyInternalSeparation`: the artifact's witness `C^R` is context-free and has no total PEG, with both external
statements (the PEG–SCA characterization and the multiphase lower bound) discharged by the artifact's own proofs.

`greibachHardest_not_totalPEG_noAxioms`: Greibach's hardest language is context-free and has no total PEG. If it
had one, so would it without `ε`, and so would every context-free language — the witness among them — as an inverse
image under a nonerasing homomorphism (`greibachWitness_nonerasing`, `recognizedByTotalPEG_inverseImage_nonerasing`).

`greibachHardest_not_PEL`: it is not even the language of a PEG that may loop (lean4-peg's `IsPEL`, over `Char`).
Such a PEG can be made one whose rules all terminate everywhere (`isPEL_allNtTotal`, Birman's check as Ford 2004 §5
describes it), and that one translates into a total PEG over the seven letters (`recognizedByTotalPEG_of_partialPEG`).
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

/-- **Greibach's hardest language is not a PEG language, even allowing grammars that loop.** -/
theorem greibachHardest_not_PEL : ¬ PartialPEG.IsPEL L0 := by
  intro h
  obtain ⟨g, htot, hL⟩ := PartialPEG.isPEL_allNtTotal h
  apply greibachHardest_not_totalPEG_noAxioms.2
  have hR := PartialPEG.recognizedByTotalPEG_of_partialPEG Letter.toChar Letter.toChar_injective g htot
  have heq : (fun v : List Letter => ∃ t, PartialPEG.Derives g (.nt g.start) (v.map Letter.toChar) (.ok t [])) =
      hardLanguage := by
    funext v
    exact propext (hL (v.map Letter.toChar)).symm
  rw [heq] at hR
  exact hR

end PegSeparation.Closure.GreibachHardest

#print axioms PegSeparation.CFLNotPEG.fullyInternalSeparation
#print axioms PegSeparation.Closure.GreibachHardest.greibachHardest_not_totalPEG_noAxioms
#print axioms PegSeparation.Closure.GreibachHardest.greibachHardest_not_PEL
