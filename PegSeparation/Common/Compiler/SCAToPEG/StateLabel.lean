import PegSeparation.Common.Compiler.SCAToPEG.CompilerCorrectness


namespace PegSeparation.SCAToPEG

open PegSeparation
open PegSeparation.Scaffolding

noncomputable section

section Evaluation

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
variable {stateCount workLabelCount degree radius : Nat}

local notation "G" automaton => grammar automaton

@[simp] theorem reverseConfig_cons_label
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (symbol : Terminal) (rest : List Terminal) :
    (reverseConfig automaton (symbol :: rest)).2.top.label =
      some (actionFor automaton (actualKey automaton symbol rest)).newLabel := by
  rw [reverseConfig_cons_scaffold]
  rfl

theorem evaluates_stateRule
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (wanted : Fin stateCount) (input : List Terminal)
    (recurse : ∀ (childName : Name stateCount workLabelCount degree radius)
        (childInput : List Terminal),
      nameMeasure childName childInput <
          nameMeasure (.state wanted :
            Name stateCount workLabelCount degree radius) input →
      (G automaton).Evaluates (invoke childName) childInput
        (nameResult automaton childName childInput)) :
    (G automaton).Evaluates (stateRule automaton wanted) input
      (nameResult automaton (.state wanted) input) := by
  cases input with
  | nil =>
      have dispatchFails : (G automaton).Evaluates
          (dispatch fun key =>
            if (actionFor automaton key).nextState = wanted
              then .empty else .failure) [] .failure := by
        apply evaluates_dispatch_failure
        intro key
        exact evaluates_transitionTest_empty key
      by_cases equal : wanted = automaton.initialState
      · have evaluated : (G automaton).Evaluates
            (.orderedChoice
              (endOfInput (Terminal := Terminal) (stateCount := stateCount)
                (workLabelCount := workLabelCount) (degree := degree)
                (radius := radius))
              (dispatch fun key =>
                if (actionFor automaton key).nextState = wanted
                  then .empty else .failure)) [] (.success []) :=
          .choiceLeft evaluates_endOfInput_empty
        simpa [stateRule, equal, nameResult] using evaluated
      · have evaluated : (G automaton).Evaluates
            (.orderedChoice (.failure)
              (dispatch fun key =>
                if (actionFor automaton key).nextState = wanted
                  then .empty else .failure)) [] .failure :=
          .choiceRight (.failure []) dispatchFails
        simpa [stateRule, equal, Ne.symm equal, nameResult] using evaluated
  | cons symbol rest =>
      let actual := actualKey automaton symbol rest
      have smaller (childName : Name stateCount workLabelCount degree radius) :
          nameMeasure childName rest <
            nameMeasure (.state wanted :
              Name stateCount workLabelCount degree radius) (symbol :: rest) :=
        nameMeasure_lt_of_length_lt (by simp) childName (.state wanted)
      have stateActual : (G automaton).Evaluates
          (invoke (.state actual.state)) rest (.success rest) := by
        have evaluated := recurse (.state actual.state) rest
          (smaller (.state actual.state))
        simpa [nameResult, actual, actualKey] using evaluated
      have hoodActual : (G automaton).Evaluates
          (invoke (.hood actual.view)) rest (.success rest) := by
        have evaluated := recurse (.hood actual.view) rest
          (smaller (.hood actual.view))
        simpa [nameResult, actual, actualKey] using evaluated
      have actualTest : (G automaton).Evaluates
          (transitionTest actual) (symbol :: rest)
            (.success (symbol :: rest)) := by
        simpa [actual, actualKey] using
          (evaluates_transitionTest_actual actual rest stateActual hoodActual)
      have otherTests : ∀ key, key ≠ actual →
          (G automaton).Evaluates
            (transitionTest key) (symbol :: rest) .failure := by
        intro key different
        have stateEvaluation := recurse (.state key.state) rest
          (smaller (.state key.state))
        have hoodEvaluation := recurse (.hood key.view) rest
          (smaller (.hood key.view))
        apply evaluates_transitionTest_other actual key rest different
        · simpa [nameResult, actual, actualKey, eq_comm] using stateEvaluation
        · simpa [nameResult, actual, actualKey, eq_comm] using hoodEvaluation
      have continuation : (G automaton).Evaluates
          (if (actionFor automaton actual).nextState = wanted
            then .empty else .failure) (symbol :: rest)
          (if (actionFor automaton actual).nextState = wanted
            then .success (symbol :: rest) else .failure) := by
        by_cases equal : (actionFor automaton actual).nextState = wanted
        · simpa [equal] using
            (PegGrammar.Evaluates.empty (grammar := G automaton) (symbol :: rest))
        · simpa [equal] using
            (PegGrammar.Evaluates.failure (grammar := G automaton) (symbol :: rest))
      have dispatched : (G automaton).Evaluates
          (dispatch fun key =>
            if (actionFor automaton key).nextState = wanted
              then .empty else .failure) (symbol :: rest)
          (if (actionFor automaton actual).nextState = wanted
            then .success (symbol :: rest) else .failure) := by
        exact evaluates_dispatch_of_unique actualTest continuation otherTests
      have firstFails : (G automaton).Evaluates
          (if wanted = automaton.initialState then
            endOfInput (Terminal := Terminal) (stateCount := stateCount)
              (workLabelCount := workLabelCount) (degree := degree)
              (radius := radius)
          else .failure) (symbol :: rest) .failure := by
        by_cases equal : wanted = automaton.initialState
        · simpa [equal] using
            (evaluates_endOfInput_cons (grammar := G automaton) symbol rest)
        · simpa [equal] using
            (PegGrammar.Evaluates.failure (grammar := G automaton)
              (symbol :: rest))
      have evaluated := PegGrammar.Evaluates.choiceRight firstFails dispatched
      change (G automaton).Evaluates (stateRule automaton wanted)
        (symbol :: rest)
        (if (reverseConfig automaton (symbol :: rest)).1 = wanted
          then .success (symbol :: rest) else .failure)
      rw [reverseConfig_cons_state]
      simpa [stateRule, actual] using evaluated

theorem evaluates_labelRule
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (wanted : Fin workLabelCount) (input : List Terminal)
    (recurse : ∀ (childName : Name stateCount workLabelCount degree radius)
        (childInput : List Terminal),
      nameMeasure childName childInput <
          nameMeasure (.label wanted :
            Name stateCount workLabelCount degree radius) input →
      (G automaton).Evaluates (invoke childName) childInput
        (nameResult automaton childName childInput)) :
    (G automaton).Evaluates (labelRule automaton wanted) input
      (nameResult automaton (.label wanted) input) := by
  cases input with
  | nil =>
      have evaluated : (G automaton).Evaluates
          (dispatch fun key =>
            if (actionFor automaton key).newLabel = wanted
              then .empty else .failure) [] .failure := by
        apply evaluates_dispatch_failure
        intro key
        exact evaluates_transitionTest_empty key
      simpa [labelRule, nameResult, Automaton.initialScaffold] using evaluated
  | cons symbol rest =>
      let actual := actualKey automaton symbol rest
      have smaller (childName : Name stateCount workLabelCount degree radius) :
          nameMeasure childName rest <
            nameMeasure (.label wanted :
              Name stateCount workLabelCount degree radius) (symbol :: rest) :=
        nameMeasure_lt_of_length_lt (by simp) childName (.label wanted)
      have stateActual : (G automaton).Evaluates
          (invoke (.state actual.state)) rest (.success rest) := by
        have evaluated := recurse (.state actual.state) rest
          (smaller (.state actual.state))
        simpa [nameResult, actual, actualKey] using evaluated
      have hoodActual : (G automaton).Evaluates
          (invoke (.hood actual.view)) rest (.success rest) := by
        have evaluated := recurse (.hood actual.view) rest
          (smaller (.hood actual.view))
        simpa [nameResult, actual, actualKey] using evaluated
      have actualTest : (G automaton).Evaluates
          (transitionTest actual) (symbol :: rest)
            (.success (symbol :: rest)) := by
        simpa [actual, actualKey] using
          (evaluates_transitionTest_actual actual rest stateActual hoodActual)
      have otherTests : ∀ key, key ≠ actual →
          (G automaton).Evaluates
            (transitionTest key) (symbol :: rest) .failure := by
        intro key different
        have stateEvaluation := recurse (.state key.state) rest
          (smaller (.state key.state))
        have hoodEvaluation := recurse (.hood key.view) rest
          (smaller (.hood key.view))
        apply evaluates_transitionTest_other actual key rest different
        · simpa [nameResult, actual, actualKey, eq_comm] using stateEvaluation
        · simpa [nameResult, actual, actualKey, eq_comm] using hoodEvaluation
      have continuation : (G automaton).Evaluates
          (if (actionFor automaton actual).newLabel = wanted
            then .empty else .failure) (symbol :: rest)
          (if (actionFor automaton actual).newLabel = wanted
            then .success (symbol :: rest) else .failure) := by
        by_cases equal : (actionFor automaton actual).newLabel = wanted
        · simpa [equal] using
            (PegGrammar.Evaluates.empty (grammar := G automaton) (symbol :: rest))
        · simpa [equal] using
            (PegGrammar.Evaluates.failure (grammar := G automaton) (symbol :: rest))
      have dispatched : (G automaton).Evaluates
          (dispatch fun key =>
            if (actionFor automaton key).newLabel = wanted
              then .empty else .failure) (symbol :: rest)
          (if (actionFor automaton actual).newLabel = wanted
            then .success (symbol :: rest) else .failure) := by
        exact evaluates_dispatch_of_unique actualTest continuation otherTests
      change (G automaton).Evaluates (labelRule automaton wanted)
        (symbol :: rest)
        (if (reverseConfig automaton (symbol :: rest)).2.top.label = some wanted
          then .success (symbol :: rest) else .failure)
      rw [reverseConfig_cons_label]
      simp only [Option.some.injEq]
      unfold labelRule
      exact dispatched

end Evaluation

end

end PegSeparation.SCAToPEG
