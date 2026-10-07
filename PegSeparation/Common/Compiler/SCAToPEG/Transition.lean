import PegSeparation.Common.Compiler.SCAToPEG.Evaluation


namespace PegSeparation.SCAToPEG

open PegSeparation

noncomputable section

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
variable {stateCount workLabelCount degree radius : Nat}

local notation "Key" =>
  TransitionKey Terminal stateCount workLabelCount degree radius

variable {grammar :
  PegGrammar Terminal (NameCount stateCount workLabelCount degree radius)}

theorem evaluates_transitionTest_actual
    (actual : Key) (rest : List Terminal)
    (stateSucceeds : grammar.Evaluates
      (invoke (.state actual.state)) rest (.success rest))
    (hoodSucceeds : grammar.Evaluates
      (invoke (.hood actual.view)) rest (.success rest)) :
    grammar.Evaluates (transitionTest actual) (actual.symbol :: rest)
      (.success (actual.symbol :: rest)) := by
  unfold transitionTest
  apply PegGrammar.Evaluates.sequenceSuccess
  · apply PegGrammar.Evaluates.andSuccess
    exact .sequenceSuccess
      (evaluates_terminal_match actual.symbol rest) stateSucceeds
  · apply PegGrammar.Evaluates.andSuccess
    exact .sequenceSuccess
      (evaluates_terminal_match actual.symbol rest) hoodSucceeds

theorem evaluates_transitionTest_empty (key : Key) :
    grammar.Evaluates (transitionTest key) [] .failure := by
  unfold transitionTest
  apply PegGrammar.Evaluates.sequenceFailure
  apply PegGrammar.Evaluates.andFailure
  exact .sequenceFailure (evaluates_terminal_empty key.symbol)

theorem evaluates_transitionTest_other
    (actual key : Key) (rest : List Terminal)
    (different : key ≠ actual)
    (stateEvaluation : grammar.Evaluates
      (invoke (.state key.state)) rest
      (if key.state = actual.state then .success rest else .failure))
    (hoodEvaluation : grammar.Evaluates
      (invoke (.hood key.view)) rest
      (if key.view = actual.view then .success rest else .failure)) :
    grammar.Evaluates (transitionTest key) (actual.symbol :: rest) .failure := by
  unfold transitionTest
  by_cases symbolEqual : key.symbol = actual.symbol
  · by_cases stateEqual : key.state = actual.state
    · have viewDifferent : key.view ≠ actual.view := by
        intro viewEqual
        apply different
        cases key
        cases actual
        simp_all
      have stateSucceeds : grammar.Evaluates
          (invoke (.state key.state)) rest (.success rest) := by
        simpa [stateEqual] using stateEvaluation
      have hoodFails : grammar.Evaluates
          (invoke (.hood key.view)) rest .failure := by
        simpa [viewDifferent] using hoodEvaluation
      apply PegGrammar.Evaluates.sequenceSuccess
      · apply PegGrammar.Evaluates.andSuccess
        exact .sequenceSuccess
          (by simpa [symbolEqual] using
            (evaluates_terminal_match (grammar := grammar) key.symbol rest))
          stateSucceeds
      · apply PegGrammar.Evaluates.andFailure
        exact .sequenceSuccess
          (by simpa [symbolEqual] using
            (evaluates_terminal_match (grammar := grammar) key.symbol rest))
          hoodFails
    · have stateFails : grammar.Evaluates
          (invoke (.state key.state)) rest .failure := by
        simpa [stateEqual] using stateEvaluation
      apply PegGrammar.Evaluates.sequenceFailure
      apply PegGrammar.Evaluates.andFailure
      exact .sequenceSuccess
        (by simpa [symbolEqual] using
          (evaluates_terminal_match (grammar := grammar) key.symbol rest))
        stateFails
  · apply PegGrammar.Evaluates.sequenceFailure
    apply PegGrammar.Evaluates.andFailure
    exact .sequenceFailure
      (evaluates_terminal_mismatch (grammar := grammar)
        (Ne.symm symbolEqual) rest)

theorem evaluates_transitionTest_canonical
    (actual key : Key) (rest : List Terminal)
    (stateEvaluation : grammar.Evaluates
      (invoke (.state key.state)) rest
      (if key.state = actual.state then .success rest else .failure))
    (hoodEvaluation : grammar.Evaluates
      (invoke (.hood key.view)) rest
      (if key.view = actual.view then .success rest else .failure)) :
    grammar.Evaluates (transitionTest key) (actual.symbol :: rest)
      (if key = actual then .success (actual.symbol :: rest) else .failure) := by
  by_cases equal : key = actual
  · subst key
    simpa using evaluates_transitionTest_actual actual rest
      (by simpa using stateEvaluation) (by simpa using hoodEvaluation)
  · simpa [equal] using evaluates_transitionTest_other actual key rest equal
      stateEvaluation hoodEvaluation

end

end PegSeparation.SCAToPEG
