import PegSeparation.CFLNotPEG.Main
import PegSeparation.Closure.BooleanClosure
import PegSeparation.Closure.InverseHomomorphism
import PegSeparation.Closure.RegularToPEG


namespace PegSeparation.Closure.GreibachHardest

open PegSeparation

universe u


structure Witness where
  HardAlphabet : Type
  hardAlphabetFintype : Fintype HardAlphabet
  hardAlphabetDecidableEq : DecidableEq HardAlphabet
  language : Language HardAlphabet
  isContextFree : language.IsContextFree
  reduction :
    ∀ (Source : Type) (_ : Fintype Source) (_ : DecidableEq Source)
      (sourceLanguage : Language Source),
      sourceLanguage.IsContextFree →
        ∃ hom : WordHom Source HardAlphabet,
          sourceLanguage = hom.inverseImage language ∨
            sourceLanguage =
              hom.inverseImage (language - (1 : Language HardAlphabet))

abbrev Statement : Prop :=
  Nonempty Witness

def Witness.IsTotalPEG (hardest : Witness) : Prop :=
  @PegSeparation.RecognizedByTotalPEG
    hardest.HardAlphabet hardest.hardAlphabetDecidableEq hardest.language


private def epsilonDFA (Alphabet : Type u) : DFA Alphabet Bool where
  step := fun _ _ => false
  start := true
  accept := {true}

private theorem epsilonDFA_evalFrom_false
    {Alphabet : Type u} (word : List Alphabet) :
    (epsilonDFA Alphabet).evalFrom false word = false := by
  induction word with
  | nil => rfl
  | cons letter rest induction =>
      change (epsilonDFA Alphabet).evalFrom false rest = false
      exact induction

private theorem epsilonDFA_accepts_iff
    {Alphabet : Type u} (word : List Alphabet) :
    word ∈ (epsilonDFA Alphabet).accepts ↔ word = [] := by
  cases word with
  | nil => simp [epsilonDFA, DFA.mem_accepts, DFA.eval]
  | cons letter rest =>
      rw [DFA.mem_accepts]
      simp only [List.cons_ne_nil, iff_false]
      change
        (epsilonDFA Alphabet).evalFrom false rest ∉ ({true} : Set Bool)
      rw [epsilonDFA_evalFrom_false]
      simp

theorem epsilonLanguage_isRegular
    {Alphabet : Type u} :
    (1 : Language Alphabet).IsRegular := by
  refine ⟨Bool, inferInstance, epsilonDFA Alphabet, ?_⟩
  apply Language.ext
  intro word
  rw [epsilonDFA_accepts_iff, Language.mem_one]

theorem sub_epsilon_eq_inter_compl
    {Alphabet : Type u} (language : Language Alphabet) :
    language - (1 : Language Alphabet) =
      language ⊓ (1 : Language Alphabet)ᶜ := by
  apply Language.ext
  intro word
  rfl

set_option linter.unusedFintypeInType false in
theorem recognizedByTotalPEG_sub_epsilon
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {language : Language Alphabet}
    (recognized : PegSeparation.RecognizedByTotalPEG language) :
    PegSeparation.RecognizedByTotalPEG
      (language - (1 : Language Alphabet)) := by
  have complementRegular :
      ((1 : Language Alphabet)ᶜ).IsRegular :=
    epsilonLanguage_isRegular.compl
  have intersectionRecognized :
      PegSeparation.RecognizedByTotalPEG
        (language ⊓ (1 : Language Alphabet)ᶜ) :=
    recognizedByTotalPEG_inter recognized
      (recognizedByTotalPEG_of_isRegular complementRegular)
  rw [sub_epsilon_eq_inter_compl]
  exact intersectionRecognized


theorem Witness.not_isTotalPEG
    (hardest : Witness)
    (inverseImageClosure :
      ∀ (hom : WordHom
          PegSeparation.CFLNotPEG.ConcreteAlphabet hardest.HardAlphabet)
        {targetLanguage : Language hardest.HardAlphabet},
        @PegSeparation.RecognizedByTotalPEG
            hardest.HardAlphabet hardest.hardAlphabetDecidableEq
            targetLanguage →
          PegSeparation.RecognizedByTotalPEG
            (hom.inverseImage targetLanguage)) :
    ¬ hardest.IsTotalPEG := by
  intro hardRecognized
  letI : Fintype hardest.HardAlphabet :=
    hardest.hardAlphabetFintype
  letI : DecidableEq hardest.HardAlphabet :=
    hardest.hardAlphabetDecidableEq
  have hardWithoutEpsilonRecognized :
      PegSeparation.RecognizedByTotalPEG
        (hardest.language - (1 : Language hardest.HardAlphabet)) :=
    recognizedByTotalPEG_sub_epsilon hardRecognized
  obtain ⟨hom, reduction | reduction⟩ :=
    hardest.reduction
      PegSeparation.CFLNotPEG.ConcreteAlphabet
      inferInstance inferInstance
      PegSeparation.CFLNotPEG.WitnessLanguage
      PegSeparation.CFLNotPEG.finalSeparation.1
  · apply PegSeparation.CFLNotPEG.finalSeparation.2
    rw [reduction]
    exact inverseImageClosure hom hardRecognized
  · apply PegSeparation.CFLNotPEG.finalSeparation.2
    rw [reduction]
    exact inverseImageClosure hom hardWithoutEpsilonRecognized

theorem Witness.not_isTotalPEG_of_inverseHomomorphismClosure
    (hardest : Witness) :
    ¬ hardest.IsTotalPEG := by
  apply hardest.not_isTotalPEG
  intro hom targetLanguage recognized
  letI : Fintype hardest.HardAlphabet :=
    hardest.hardAlphabetFintype
  letI : DecidableEq hardest.HardAlphabet :=
    hardest.hardAlphabetDecidableEq
  exact recognizedByTotalPEG_inverseImage hom recognized

end PegSeparation.Closure.GreibachHardest

namespace PegSeparation.External.Greibach1973

axiom hardestContextFreeLanguage :
  PegSeparation.Closure.GreibachHardest.Statement

end PegSeparation.External.Greibach1973

namespace PegSeparation.Closure.GreibachHardest

noncomputable def fixedWitness : Witness :=
  Classical.choice PegSeparation.External.Greibach1973.hardestContextFreeLanguage

theorem fixedWitness_not_isTotalPEG :
    ¬ fixedWitness.IsTotalPEG :=
  fixedWitness.not_isTotalPEG_of_inverseHomomorphismClosure

theorem greibachHardest_isContextFree_not_totalPEG :
    fixedWitness.language.IsContextFree ∧
      ¬ fixedWitness.IsTotalPEG :=
  ⟨fixedWitness.isContextFree, fixedWitness_not_isTotalPEG⟩

end PegSeparation.Closure.GreibachHardest

#check PegSeparation.Closure.GreibachHardest.greibachHardest_isContextFree_not_totalPEG

#print axioms PegSeparation.Closure.GreibachHardest.epsilonLanguage_isRegular
#print axioms PegSeparation.Closure.GreibachHardest.recognizedByTotalPEG_sub_epsilon
#print axioms PegSeparation.Closure.GreibachHardest.Witness.not_isTotalPEG
#print axioms PegSeparation.Closure.GreibachHardest.greibachHardest_isContextFree_not_totalPEG
