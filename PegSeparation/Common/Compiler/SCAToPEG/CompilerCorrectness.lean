import PegSeparation.Common.Compiler.SCAToPEG.Correctness
import PegSeparation.Common.Compiler.SCAToPEG.Transition


namespace PegSeparation.SCAToPEG

open PegSeparation
open PegSeparation.Scaffolding

noncomputable section

section Evaluation

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
variable {stateCount workLabelCount degree radius : Nat}

local notation "G" automaton => grammar automaton

theorem evaluates_constraint_sequence
    {Index : Type}
    {grammar' : PegGrammar Terminal
      (NameCount stateCount workLabelCount degree radius)}
    (constraint : Index → ParsingExpression Terminal
      (NameCount stateCount workLabelCount degree radius))
    (predicate : Index → Prop) [DecidablePred predicate]
    (indices : List Index) (input : List Terminal)
    (evaluates : ∀ index, grammar'.Evaluates (constraint index) input
      (if predicate index then .success input else .failure)) :
    grammar'.Evaluates (sequences (indices.map constraint)) input
      (if ∀ index ∈ indices, predicate index then .success input else .failure) := by
  induction indices with
  | nil =>
      simpa [sequences] using (PegGrammar.Evaluates.empty (grammar := grammar') input)
  | cons index indices ih =>
      simp only [List.map_cons, sequences]
      have headEvaluation := evaluates index
      have tailEvaluation := ih
      by_cases headTrue : predicate index
      · rw [if_pos headTrue] at headEvaluation
        by_cases tailTrue : ∀ child ∈ indices, predicate child
        · rw [if_pos tailTrue] at tailEvaluation
          have allTrue : ∀ child ∈ index :: indices, predicate child := by
            intro child member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact headTrue
            · exact tailTrue child member
          rw [if_pos allTrue]
          exact .sequenceSuccess headEvaluation tailEvaluation
        · rw [if_neg tailTrue] at tailEvaluation
          have notAll : ¬∀ child ∈ index :: indices, predicate child := by
            intro allTrue
            apply tailTrue
            intro child member
            exact allTrue child (by simp [member])
          rw [if_neg notAll]
          exact .sequenceSuccess headEvaluation tailEvaluation
      · rw [if_neg headTrue] at headEvaluation
        have notAll : ¬∀ child ∈ index :: indices, predicate child := by
          intro allTrue
          exact headTrue (allTrue index (by simp))
        rw [if_neg notAll]
        exact .sequenceFailure headEvaluation

theorem evaluates_observationConstraint
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (expected : Neighborhood (Fin workLabelCount) degree radius)
    (path : BoundedPath degree radius) (input : List Terminal)
    (recurse : ∀ (childName : Name stateCount workLabelCount degree radius)
        (childInput : List Terminal),
      nameMeasure childName childInput <
          nameMeasure (.hood expected :
            Name stateCount workLabelCount degree radius) input →
      (G automaton).Evaluates (invoke childName) childInput
        (nameResult automaton childName childInput)) :
    (G automaton).Evaluates (observationConstraint expected path) input
      (if View.observe
          ((reverseConfig automaton input).2.topNeighborhood radius) path =
            View.observe expected path
        then .success input else .failure) := by
  have pathRank : nameRank (.path path :
      Name stateCount workLabelCount degree radius) <
        nameRank (.hood expected :
          Name stateCount workLabelCount degree radius) := by
    simp only [nameRank]
    omega
  have pathEvaluation := recurse (.path path) input
    (nameMeasure_lt_of_rank_lt input pathRank)
  cases followed : Scaffold.follow
      (reverseConfig automaton input).2.nodes 0 path.1 with
  | none =>
      have actualObservation : View.observe
          ((reverseConfig automaton input).2.topNeighborhood radius) path = none :=
        (observe_reverseConfig_eq_none_iff automaton input path).2 followed
      have pathFails : (G automaton).Evaluates (invoke (.path path)) input .failure := by
        simpa [nameResult, pathResult, followed] using pathEvaluation
      cases expectedObservation : View.observe expected path with
      | none =>
          simpa [observationConstraint, expectedObservation, actualObservation] using
            (PegGrammar.Evaluates.notSuccess pathFails)
      | some expectedLabel =>
          cases expectedLabel with
          | none =>
              simpa [observationConstraint, expectedObservation, actualObservation] using
                (PegGrammar.Evaluates.sequenceFailure
                  (PegGrammar.Evaluates.andFailure pathFails))
          | some label =>
              simpa [observationConstraint, expectedObservation, actualObservation] using
                (PegGrammar.Evaluates.sequenceFailure
                  (PegGrammar.Evaluates.andFailure pathFails))
  | some endpoint =>
      let endpointInput := input.drop endpoint
      let endpointLabel := (reverseConfig automaton endpointInput).2.top.label
      have actualObservation : View.observe
          ((reverseConfig automaton input).2.topNeighborhood radius) path =
            some endpointLabel := by
        simpa [endpointInput, endpointLabel] using
          observe_reverseConfig_of_follow automaton input path endpoint followed
      have pathSucceeds : (G automaton).Evaluates (invoke (.path path)) input
          (.success endpointInput) := by
        simpa [nameResult, pathResult, followed, endpointInput] using pathEvaluation
      have endpointLength : endpointInput.length ≤ input.length := by
        simp [endpointInput]
      have labelEvaluation (label : Fin workLabelCount) :
          (G automaton).Evaluates (invoke (.label label)) endpointInput
            (if endpointLabel = some label then .success endpointInput else .failure) := by
        have labelRank : nameRank (.label label :
            Name stateCount workLabelCount degree radius) <
              nameRank (.hood expected :
                Name stateCount workLabelCount degree radius) := by
          simp [nameRank]
        have evaluated := recurse (.label label) endpointInput
          (nameMeasure_lt_of_length_le_rank_lt endpointLength labelRank)
        simpa [nameResult, endpointLabel, endpointInput] using evaluated
      have pathLabelEvaluation (label : Fin workLabelCount) :
          (G automaton).Evaluates (pathLabelTest path label) input
            (if endpointLabel = some label then .success endpointInput else .failure) := by
        unfold pathLabelTest
        by_cases equal : endpointLabel = some label
        · simpa [equal] using
            (PegGrammar.Evaluates.sequenceSuccess pathSucceeds
              (by simpa [equal] using labelEvaluation label))
        · simpa [equal] using
            (PegGrammar.Evaluates.sequenceSuccess pathSucceeds
              (by simpa [equal] using labelEvaluation label))
      cases expectedObservation : View.observe expected path with
      | none =>
          simpa [observationConstraint, expectedObservation, actualObservation] using
            (PegGrammar.Evaluates.notFailure pathSucceeds)
      | some expectedLabel =>
          cases expectedLabel with
          | none =>
              have first : (G automaton).Evaluates
                  (.andPredicate (invoke (.path path))) input (.success input) :=
                .andSuccess pathSucceeds
              cases labelEq : endpointLabel with
              | none =>
                  have allNegative : ∀ label : Fin workLabelCount,
                      (G automaton).Evaluates
                        (.notPredicate (pathLabelTest path label)) input
                        (.success input) := by
                    intro label
                    apply PegGrammar.Evaluates.notSuccess
                    simpa [labelEq] using pathLabelEvaluation label
                  have remaining : (G automaton).Evaluates
                      (sequences ((Finset.univ.toList : List (Fin workLabelCount)).map
                        fun label => .notPredicate (pathLabelTest path label))) input
                      (.success input) := by
                    apply evaluates_sequences_success_same_input
                    intro expression expressionMem
                    simp only [List.mem_map] at expressionMem
                    obtain ⟨label, _, rfl⟩ := expressionMem
                    exact allNegative label
                  simpa [observationConstraint, expectedObservation,
                    actualObservation, endpointLabel, labelEq] using
                      (PegGrammar.Evaluates.sequenceSuccess first remaining)
              | some actualLabel =>
                  have labelsContain : actualLabel ∈
                      (Finset.univ.toList : List (Fin workLabelCount)) := by simp
                  have remaining : (G automaton).Evaluates
                      (sequences ((Finset.univ.toList : List (Fin workLabelCount)).map
                        fun label => .notPredicate (pathLabelTest path label))) input
                      .failure := by
                    have failureOfMem : ∀ labels : List (Fin workLabelCount),
                        actualLabel ∈ labels →
                        (G automaton).Evaluates
                          (sequences (labels.map fun label =>
                            .notPredicate (pathLabelTest path label))) input
                          .failure := by
                      intro labels member
                      induction labels with
                      | nil => simp at member
                      | cons label labels ih =>
                          simp only [List.map_cons, sequences]
                          by_cases equal : label = actualLabel
                          · subst label
                            apply PegGrammar.Evaluates.sequenceFailure
                            apply PegGrammar.Evaluates.notFailure
                            simpa [endpointLabel, labelEq] using
                              pathLabelEvaluation actualLabel
                          · apply PegGrammar.Evaluates.sequenceSuccess
                            · apply PegGrammar.Evaluates.notSuccess
                              have different : endpointLabel ≠ some label := by
                                simp [endpointLabel, labelEq, Ne.symm equal]
                              simpa [different] using pathLabelEvaluation label
                            · apply ih
                              simpa [Ne.symm equal] using member
                    exact failureOfMem _ labelsContain
                  simpa [observationConstraint, expectedObservation,
                    actualObservation, endpointLabel, labelEq] using
                      (PegGrammar.Evaluates.sequenceSuccess first remaining)
          | some expectedLabel =>
              have first : (G automaton).Evaluates
                  (.andPredicate (invoke (.path path))) input (.success input) :=
                .andSuccess pathSucceeds
              by_cases equal : endpointLabel = some expectedLabel
              · have second : (G automaton).Evaluates
                    (.andPredicate (pathLabelTest path expectedLabel)) input
                    (.success input) :=
                  .andSuccess (by simpa [equal] using
                    pathLabelEvaluation expectedLabel)
                simpa [observationConstraint, expectedObservation,
                  actualObservation, equal] using
                    (PegGrammar.Evaluates.sequenceSuccess first second)
              · have second : (G automaton).Evaluates
                    (.andPredicate (pathLabelTest path expectedLabel)) input
                    .failure :=
                  .andFailure (by simpa [equal] using
                    pathLabelEvaluation expectedLabel)
                simpa [observationConstraint, expectedObservation,
                  actualObservation, equal] using
                    (PegGrammar.Evaluates.sequenceSuccess first second)

theorem evaluates_hoodRule
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (expected : Neighborhood (Fin workLabelCount) degree radius)
    (input : List Terminal)
    (recurse : ∀ (childName : Name stateCount workLabelCount degree radius)
        (childInput : List Terminal),
      nameMeasure childName childInput <
          nameMeasure (.hood expected :
            Name stateCount workLabelCount degree radius) input →
      (G automaton).Evaluates (invoke childName) childInput
        (nameResult automaton childName childInput)) :
    (G automaton).Evaluates (hoodRule expected) input
      (if (reverseConfig automaton input).2.topNeighborhood radius = expected
        then .success input else .failure) := by
  let paths := (Finset.univ.toList : List (BoundedPath degree radius))
  have each (path : BoundedPath degree radius) :=
    evaluates_observationConstraint automaton expected path input recurse
  have sequenceEvaluation := evaluates_constraint_sequence
    (grammar' := G automaton)
    (constraint := observationConstraint expected)
    (predicate := fun path => View.observe
      ((reverseConfig automaton input).2.topNeighborhood radius) path =
        View.observe expected path)
    paths input each
  unfold hoodRule
  change (G automaton).Evaluates
    (sequences (paths.map (observationConstraint expected))) input _
  by_cases equal :
      (reverseConfig automaton input).2.topNeighborhood radius = expected
  · have allEqual : ∀ path ∈ paths,
        View.observe
            ((reverseConfig automaton input).2.topNeighborhood radius) path =
          View.observe expected path := by
      intro path _
      rw [equal]
    rw [if_pos allEqual] at sequenceEvaluation
    rw [if_pos equal]
    exact sequenceEvaluation
  · have notAll : ¬∀ path ∈ paths,
        View.observe
            ((reverseConfig automaton input).2.topNeighborhood radius) path =
          View.observe expected path := by
      intro allEqual
      apply equal
      apply View.ext_of_observe_eq
      intro path
      exact allEqual path (by simp [paths])
    rw [if_neg notAll] at sequenceEvaluation
    rw [if_neg equal]
    exact sequenceEvaluation

end Evaluation

end

end PegSeparation.SCAToPEG
