import PegSeparation.Closure.Assembly


namespace PegSeparation.Closure

open Computability
open PegSeparation.Witness.LanguageCFG


def kleenePlus {Terminal : Type} (L : Language Terminal) :
    Language Terminal :=
  L * L∗

@[simp] theorem one_add_kleenePlus_eq_kstar
    {Terminal : Type} (L : Language Terminal) :
    1 + kleenePlus L = L∗ := by
  simpa [kleenePlus] using
    Language.one_add_self_mul_kstar_eq_kstar L


noncomputable def epsilonGrammar
    (Terminal : Type) [Fintype Terminal] :
    PegGrammar Terminal 1 where
  rule := fun _ => endOfInput Terminal 1
  start := 0

@[simp] theorem epsilonGrammar_rule
    (Terminal : Type) [Fintype Terminal] (name : Fin 1) :
    (epsilonGrammar Terminal).rule name = endOfInput Terminal 1 :=
  rfl

@[simp] theorem epsilonGrammar_start
    (Terminal : Type) [Fintype Terminal] :
    (epsilonGrammar Terminal).start = 0 :=
  rfl

theorem epsilonGrammar_isLoffTotal
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal] :
    (epsilonGrammar Terminal).IsLoffTotal := by
  apply PegGrammar.PartialTotalityHelpers.loffTotal_of_nonterminal_total
  intro name input
  have hname : name = 0 := Fin.eq_zero name
  subst name
  cases input with
  | nil =>
      exact
        ⟨.success [],
          PegGrammar.Evaluates.nonterminal
            (by
              rw [epsilonGrammar_rule]
              exact evaluates_endOfInput_nil (epsilonGrammar Terminal))⟩
  | cons head tail =>
      exact
        ⟨.failure,
          PegGrammar.Evaluates.nonterminal
            (by
              rw [epsilonGrammar_rule]
              exact evaluates_endOfInput_cons
                (epsilonGrammar Terminal) head tail)⟩

theorem epsilonGrammar_recognizes_iff
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    (input : List Terminal) :
    (epsilonGrammar Terminal).Recognizes input ↔ input = [] := by
  constructor
  · intro recognized
    cases input with
    | nil => rfl
    | cons head tail =>
        have fails :
            (epsilonGrammar Terminal).Evaluates
              (.nonterminal (epsilonGrammar Terminal).start)
              (head :: tail) .failure :=
          PegGrammar.Evaluates.nonterminal
            (by
              rw [epsilonGrammar_rule]
              exact evaluates_endOfInput_cons
                (epsilonGrammar Terminal) head tail)
        exact absurd
          (External.LoffForwardRepaired.PegGrammar.evaluates_deterministic
            fails recognized)
          (by simp)
  · rintro rfl
    exact
      PegGrammar.Evaluates.nonterminal
        (by
          rw [epsilonGrammar_rule]
          exact evaluates_endOfInput_nil (epsilonGrammar Terminal))

set_option linter.unusedFintypeInType false in
theorem epsilonLanguage_isPEG
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal] :
    PegSeparation.RecognizedByTotalPEG (1 : Language Terminal) := by
  refine
    ⟨1, epsilonGrammar Terminal, epsilonGrammar_isLoffTotal,
      fun input => ?_⟩
  simpa only [Language.mem_one] using
    epsilonGrammar_recognizes_iff input


theorem kleenePlus_nonclosure
    (external : PegSeparation.ExternalAssumptions) :
    PegSeparation.RecognizedByTotalPEG StarWitness ∧
      ¬ PegSeparation.RecognizedByTotalPEG
        (kleenePlus StarWitness) := by
  refine ⟨starWitness_isPEG, ?_⟩
  intro plusRecognized
  have starRecognized :
      PegSeparation.RecognizedByTotalPEG
        ((1 : Language Terminal) + kleenePlus StarWitness) :=
    recognizedByTotalPEG_union epsilonLanguage_isPEG plusRecognized
  rw [one_add_kleenePlus_eq_kstar] at starRecognized
  exact (star_nonclosure external).2 starRecognized

theorem recognizedByTotalPEG_not_closed_kleenePlus
    (external : PegSeparation.ExternalAssumptions) :
    ∃ L : Language Terminal,
      PegSeparation.RecognizedByTotalPEG L ∧
        ¬ PegSeparation.RecognizedByTotalPEG (kleenePlus L) :=
  ⟨StarWitness, kleenePlus_nonclosure external⟩

end PegSeparation.Closure
