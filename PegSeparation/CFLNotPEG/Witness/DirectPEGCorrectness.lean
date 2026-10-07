import PegSeparation.CFLNotPEG.Witness.DirectPEGRecordScanners
import PegSeparation.CFLNotPEG.Witness.DirectPEGKeyHitScanner
import PegSeparation.CFLNotPEG.Witness.DirectPEGTotality


namespace PegSeparation.Witness.DirectPEG

open PegSeparation

namespace Correctness

open KeyHitScanner

theorem search_success_sound
    {input remaining : Word}
    (evaluation :
      grammar.Evaluates
        (.nonterminal searchName) input (.success remaining)) :
    SearchResidual input remaining := by
  cases evaluation with
  | nonterminal body =>
      rw [grammar_rule_search] at body
      change grammar.Evaluates
        (.orderedChoice
          (.nonterminal hitName)
          (.sequence
            (.nonterminal entryName)
            (.nonterminal searchName)))
        input (.success remaining) at body
      cases body with
      | choiceLeft hitEvaluation =>
          exact hit_success_sound hitEvaluation
      | choiceRight _ recursive =>
          cases recursive with
          | sequenceSuccess entryEvaluation searchEvaluation =>
              rcases entry_success_sound entryEvaluation with
                ⟨record, valid, inputEquation⟩
              rcases search_success_sound searchEvaluation with
                ⟨suffixDerivation, remainingEquation⟩
              refine ⟨?_, remainingEquation⟩
              rw [inputEquation]
              exact LanguageCFG.Grammar.A.skip
                (LanguageCFG.Grammar.E.complete record valid)
                suffixDerivation
termination_by input.length
decreasing_by
  rw [inputEquation]
  simp [LanguageCFG.recordWord]
  omega

theorem search_complete
    {input : Word} (derivation : LanguageCFG.Grammar.A input) :
    grammar.Evaluates
      (.nonterminal searchName) input (.success []) := by
  induction derivation with
  | @skip entry suffix entryDerivation suffixDerivation
      inductionHypothesis =>
      obtain ⟨record, valid, entryEquation⟩ :=
        entryDerivation.sound
      have entryEvaluation :
          grammar.Evaluates
            (.nonterminal entryName)
            (entry ++ suffix)
            (.success suffix) := by
        rw [entryEquation]
        exact entry_complete record suffix valid
      obtain ⟨hitResult, hitEvaluation⟩ :=
        nonterminal_call_total hitName (entry ++ suffix)
      apply PegGrammar.Evaluates.nonterminal
      rw [grammar_rule_search]
      change grammar.Evaluates
        (.orderedChoice
          (.nonterminal hitName)
          (.sequence
            (.nonterminal entryName)
            (.nonterminal searchName)))
        (entry ++ suffix) (.success [])
      cases hitResult with
      | failure =>
          exact .choiceRight hitEvaluation
            (.sequenceSuccess entryEvaluation inductionHypothesis)
      | success remaining =>
          rcases hit_success_sound hitEvaluation with
            ⟨_, remainingEquation⟩
          subst remaining
          exact .choiceLeft hitEvaluation
  | @witnessZero word derivation =>
      have witness :
          CurrentWitness
            (.langle :: .bit0 :: (word ++ [.bit0])) :=
        ⟨false, word, derivation, rfl⟩
      have hitEvaluation := hit_complete witness
      apply PegGrammar.Evaluates.nonterminal
      rw [grammar_rule_search]
      change grammar.Evaluates
        (.orderedChoice
          (.nonterminal hitName)
          (.sequence
            (.nonterminal entryName)
            (.nonterminal searchName)))
        (.langle :: .bit0 :: (word ++ [.bit0]))
        (.success [])
      exact .choiceLeft hitEvaluation
  | @witnessOne word derivation =>
      have witness :
          CurrentWitness
            (.langle :: .bit1 :: (word ++ [.bit1])) :=
        ⟨true, word, derivation, rfl⟩
      have hitEvaluation := hit_complete witness
      apply PegGrammar.Evaluates.nonterminal
      rw [grammar_rule_search]
      change grammar.Evaluates
        (.orderedChoice
          (.nonterminal hitName)
          (.sequence
            (.nonterminal entryName)
            (.nonterminal searchName)))
        (.langle :: .bit1 :: (word ++ [.bit1]))
        (.success [])
      exact .choiceLeft hitEvaluation

theorem search_success_iff
    {input remaining : Word} :
    grammar.Evaluates
        (.nonterminal searchName) input (.success remaining) ↔
      SearchResidual input remaining := by
  constructor
  · exact search_success_sound
  · rintro ⟨derivation, rfl⟩
    exact search_complete derivation

end Correctness

theorem grammar_recognizes_iff_C (input : Word) :
    grammar.Recognizes input ↔ input ∈ LanguageCFG.C := by
  rw [← LanguageCFG.Grammar.inductive_start_iff_mem_C]
  constructor
  · intro recognized
    have evaluation :
        grammar.Evaluates
          (.nonterminal searchName) input (.success []) := by
      simpa [PegGrammar.Recognizes] using recognized
    exact (Correctness.search_success_sound evaluation).1
  · intro derivation
    have evaluation := Correctness.search_complete derivation
    simpa [PegGrammar.Recognizes] using evaluation

end PegSeparation.Witness.DirectPEG
