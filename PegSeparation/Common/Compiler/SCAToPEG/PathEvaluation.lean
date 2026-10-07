import PegSeparation.Common.Compiler.SCAToPEG.CompilerCorrectness


namespace PegSeparation.SCAToPEG

open PegSeparation
open PegSeparation.Scaffolding

noncomputable section

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
variable {stateCount workLabelCount degree radius : Nat}

local notation "G" automaton => grammar automaton

private theorem pathResult_success_length_le
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (path : BoundedPath degree radius) {input remaining : List Terminal}
    (succeeds : pathResult automaton path input = .success remaining) :
    remaining.length ≤ input.length := by
  unfold pathResult at succeeds
  split at succeeds
  · contradiction
  · rename_i endpoint followed
    have remainingEq : remaining = input.drop endpoint := by
      simpa using succeeds.symm
    subst remaining
    simp

theorem evaluates_pathRule
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (path : BoundedPath degree radius) (input : List Terminal)
    (recurse : ∀ (childName : Name stateCount workLabelCount degree radius)
        (childInput : List Terminal),
      nameMeasure childName childInput <
          nameMeasure (.path path :
            Name stateCount workLabelCount degree radius) input →
      (G automaton).Evaluates (invoke childName) childInput
        (nameResult automaton childName childInput)) :
    (G automaton).Evaluates (pathRule automaton path) input
      (pathResult automaton path input) := by
  rcases path with ⟨directions, withinRadius⟩
  cases directions with
  | nil =>
    simpa [pathRule, pathResult, Scaffold.follow, Scaffold.nodes] using
      (PegGrammar.Evaluates.empty (grammar := G automaton) input)
  | cons direction directions =>
    let tail : BoundedPath degree radius :=
      BoundedPath.tail ⟨direction :: directions, withinRadius⟩
    cases input with
    | nil =>
        have dispatchFails : (G automaton).Evaluates
            (dispatch fun key => targetContinuation automaton key
              direction tail) [] .failure := by
          apply evaluates_dispatch_failure
          intro key
          exact evaluates_transitionTest_empty key
        simpa [pathRule, pathResult, Scaffold.follow, reverseConfig_nil,
          Automaton.initialScaffold, Scaffold.nodes, BoundedPath.tail, tail]
          using dispatchFails
    | cons symbol rest =>
        let actual := actualKey automaton symbol rest
        have suffixShorter : rest.length < (symbol :: rest).length := by simp
        have stateEvaluation
            (key : TransitionKey Terminal stateCount workLabelCount degree radius) :
            (G automaton).Evaluates (invoke (.state key.state)) rest
              (if key.state = actual.state then .success rest else .failure) := by
          have evaluated := recurse (.state key.state) rest
            (nameMeasure_lt_of_length_lt suffixShorter _ _)
          simpa [nameResult, actual, actualKey, eq_comm] using evaluated
        have hoodEvaluation
            (key : TransitionKey Terminal stateCount workLabelCount degree radius) :
            (G automaton).Evaluates (invoke (.hood key.view)) rest
              (if key.view = actual.view then .success rest else .failure) := by
          have evaluated := recurse (.hood key.view) rest
            (nameMeasure_lt_of_length_lt suffixShorter _ _)
          simpa [nameResult, actual, actualKey, eq_comm] using evaluated
        have actualTest : (G automaton).Evaluates
            (transitionTest actual) (symbol :: rest)
            (.success (symbol :: rest)) := by
          simpa [actual, actualKey] using
            (evaluates_transitionTest_actual actual rest
              (by simpa using stateEvaluation actual)
              (by simpa using hoodEvaluation actual))
        have otherTestsFail
            (key : TransitionKey Terminal stateCount workLabelCount degree radius)
            (different : key ≠ actual) :
            (G automaton).Evaluates (transitionTest key) (symbol :: rest)
              .failure := by
          exact evaluates_transitionTest_other actual key rest different
            (stateEvaluation key) (hoodEvaluation key)
        have continuationEvaluation : (G automaton).Evaluates
            (targetContinuation automaton actual direction tail)
            (symbol :: rest)
            (pathResult automaton
              ⟨direction :: directions, withinRadius⟩ (symbol :: rest)) := by
          have rebuilt :
              (⟨direction :: tail.1, withinRadius⟩ :
                BoundedPath degree radius) =
                ⟨direction :: directions, withinRadius⟩ := by
            apply Subtype.ext
            simp [tail, BoundedPath.tail]
          have semantic :=
            pathResult_cons automaton direction tail withinRadius symbol rest
          rw [rebuilt] at semantic
          cases targetEq : (actionFor automaton actual).target direction with
          | missing =>
              rw [targetEq] at semantic
              rw [semantic]
              unfold targetContinuation
              rw [targetEq]
              exact .failure (symbol :: rest)
          | self =>
              rw [targetEq] at semantic
              rw [semantic]
              unfold targetContinuation
              rw [targetEq]
              have tailRank : nameRank (.path tail :
                  Name stateCount workLabelCount degree radius) <
                    nameRank (.path
                      ⟨direction :: directions, withinRadius⟩ :
                        Name stateCount workLabelCount degree radius) := by
                simp [nameRank, tail, BoundedPath.tail]
              simpa [nameResult] using recurse (.path tail) (symbol :: rest)
                (nameMeasure_lt_of_rank_lt (symbol :: rest) tailRank)
          | path oldDirections oldWithin =>
              rw [targetEq] at semantic
              rw [semantic]
              unfold targetContinuation
              rw [targetEq]
              let oldPath : BoundedPath degree radius :=
                boundedPathOfList oldDirections oldWithin
              have oldEvaluation : (G automaton).Evaluates
                  (invoke (.path oldPath)) rest
                  (pathResult automaton oldPath rest) := by
                simpa [nameResult] using recurse (.path oldPath) rest
                  (nameMeasure_lt_of_length_lt suffixShorter _ _)
              have terminalEvaluation : (G automaton).Evaluates
                  (.terminal actual.symbol) (symbol :: rest) (.success rest) := by
                simpa [actual, actualKey] using
                  (evaluates_terminal_match
                    (grammar := G automaton) symbol rest)
              cases oldResultEq : pathResult automaton oldPath rest with
              | failure =>
                  have oldFails : (G automaton).Evaluates
                      (invoke (.path oldPath)) rest .failure := by
                    simpa [oldResultEq] using oldEvaluation
                  simpa [oldPath, oldResultEq] using
                    (PegGrammar.Evaluates.sequenceSuccess terminalEvaluation
                      (PegGrammar.Evaluates.sequenceFailure oldFails))
              | success middle =>
                  have oldSucceeds : (G automaton).Evaluates
                      (invoke (.path oldPath)) rest (.success middle) := by
                    simpa [oldResultEq] using oldEvaluation
                  have middleLe : middle.length ≤ rest.length :=
                    pathResult_success_length_le automaton oldPath oldResultEq
                  have middleShorter :
                      middle.length < (symbol :: rest).length :=
                    lt_of_le_of_lt middleLe suffixShorter
                  have tailEvaluation : (G automaton).Evaluates
                      (invoke (.path tail)) middle
                      (pathResult automaton tail middle) := by
                    simpa [nameResult] using recurse (.path tail) middle
                      (nameMeasure_lt_of_length_lt middleShorter _ _)
                  simpa [oldPath, oldResultEq] using
                    (PegGrammar.Evaluates.sequenceSuccess terminalEvaluation
                      (PegGrammar.Evaluates.sequenceSuccess oldSucceeds
                        tailEvaluation))
        have dispatched := evaluates_dispatch_of_unique
          (continuation := fun key =>
            targetContinuation automaton key direction tail)
          actualTest continuationEvaluation otherTestsFail
        simpa [pathRule, tail] using dispatched

end

end PegSeparation.SCAToPEG
