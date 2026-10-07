import PegSeparation.Common.Compiler.SCAToPEG.CompilerCorrectness


namespace PegSeparation.SCAToPEG

open PegSeparation
open PegSeparation.Scaffolding

noncomputable section

section Evaluation

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
variable {stateCount workLabelCount degree radius : Nat}

local notation "G" automaton => grammar automaton

private theorem evaluates_consumeChoices_of_mem
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (symbols : List Terminal) (symbol : Terminal) (rest : List Terminal)
    (member : symbol ∈ symbols)
    (recursiveEvaluation : (G automaton).Evaluates
      (invoke (.consumeAll : Name stateCount workLabelCount degree radius)) rest
      (.success [])) :
    (G automaton).Evaluates
      (choices (symbols.map fun candidate =>
        .sequence (.terminal candidate) (invoke (.consumeAll :
          Name stateCount workLabelCount degree radius))))
      (symbol :: rest) (.success []) := by
  induction symbols with
  | nil => simp at member
  | cons candidate candidates ih =>
      by_cases equal : candidate = symbol
      · subst candidate
        apply PegGrammar.Evaluates.choiceLeft
        exact .sequenceSuccess (evaluates_terminal_match symbol rest)
          recursiveEvaluation
      · apply PegGrammar.Evaluates.choiceRight
        · exact .sequenceFailure
            (evaluates_terminal_mismatch (Ne.symm equal) rest)
        · apply ih
          simpa [Ne.symm equal] using member

theorem evaluates_consumeAllRule
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal)
    (recurse : ∀ (childName : Name stateCount workLabelCount degree radius)
        (childInput : List Terminal),
      nameMeasure childName childInput <
          nameMeasure (.consumeAll :
            Name stateCount workLabelCount degree radius) input →
      (G automaton).Evaluates (invoke childName) childInput
        (nameResult automaton childName childInput)) :
    (G automaton).Evaluates consumeAllRule input
      (nameResult automaton .consumeAll input) := by
  cases input with
  | nil =>
      unfold consumeAllRule
      apply PegGrammar.Evaluates.choiceRight
      · apply evaluates_choices_failure
        intro expression expressionMem
        simp only [List.mem_map] at expressionMem
        obtain ⟨symbol, _, rfl⟩ := expressionMem
        exact .sequenceFailure (evaluates_terminal_empty symbol)
      · simpa [nameResult] using
          (PegGrammar.Evaluates.empty (grammar := G automaton) [])
  | cons symbol rest =>
      have restShorter : rest.length < (symbol :: rest).length := by simp
      have recursiveEvaluation : (G automaton).Evaluates
          (invoke (.consumeAll :
            Name stateCount workLabelCount degree radius)) rest (.success []) := by
        have evaluated := recurse .consumeAll rest
          (nameMeasure_lt_of_length_lt restShorter .consumeAll .consumeAll)
        simpa [nameResult] using evaluated
      have member : symbol ∈ (Finset.univ.toList : List Terminal) := by simp
      have left : (G automaton).Evaluates
          (choices ((Finset.univ.toList : List Terminal).map fun candidate =>
            .sequence (.terminal candidate) (invoke (.consumeAll :
              Name stateCount workLabelCount degree radius))))
          (symbol :: rest) (.success []) :=
        evaluates_consumeChoices_of_mem automaton _ symbol rest member
          recursiveEvaluation
      unfold consumeAllRule
      simpa [nameResult] using (PegGrammar.Evaluates.choiceLeft left)

private theorem evaluates_acceptingStateChoices
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (states : List (Fin stateCount)) (input : List Terminal)
    (stateEvaluation : ∀ state ∈ states,
      (G automaton).Evaluates (invoke (.state state)) input
        (if (reverseConfig automaton input).1 = state
          then .success input else .failure)) :
    (G automaton).Evaluates
      (choices (states.map fun state => invoke (.state state))) input
      (if (reverseConfig automaton input).1 ∈ states
        then .success input else .failure) := by
  induction states with
  | nil =>
      simpa [choices] using
        (PegGrammar.Evaluates.failure (grammar := G automaton) input)
  | cons state states ih =>
      simp only [List.map_cons, choices]
      by_cases equal : (reverseConfig automaton input).1 = state
      · have first := stateEvaluation state (by simp)
        rw [if_pos equal] at first
        simpa [equal] using (PegGrammar.Evaluates.choiceLeft first)
      · have first := stateEvaluation state (by simp)
        rw [if_neg equal] at first
        have restEvaluation := ih (by
          intro child member
          exact stateEvaluation child (by simp [member]))
        simpa [equal] using
          (PegGrammar.Evaluates.choiceRight first restEvaluation)

theorem evaluates_acceptsRule
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal)
    (recurse : ∀ (childName : Name stateCount workLabelCount degree radius)
        (childInput : List Terminal),
      nameMeasure childName childInput <
          nameMeasure (.accepts :
            Name stateCount workLabelCount degree radius) input →
      (G automaton).Evaluates (invoke childName) childInput
        (nameResult automaton childName childInput)) :
    (G automaton).Evaluates (acceptsRule automaton) input
      (nameResult automaton .accepts input) := by
  let current := (reverseConfig automaton input).1
  have stateRank (state : Fin stateCount) :
      nameRank (.state state : Name stateCount workLabelCount degree radius) <
        nameRank (.accepts : Name stateCount workLabelCount degree radius) := by
    simp [nameRank]
  have eachState (state : Fin stateCount) : (G automaton).Evaluates
      (invoke (.state state)) input
      (if current = state then .success input else .failure) := by
    have evaluated := recurse (.state state) input
      (nameMeasure_lt_of_rank_lt input (stateRank state))
    simpa [nameResult, current] using evaluated
  have stateChoices : (G automaton).Evaluates
      (choices (automaton.accepting.toList.map fun state => invoke (.state state))) input
      (if current ∈ automaton.accepting.toList
        then .success input else .failure) := by
    apply evaluates_acceptingStateChoices automaton automaton.accepting.toList input
    intro state _
    exact eachState state
  by_cases accepted : current ∈ automaton.accepting
  · have stateChoicesSuccess : (G automaton).Evaluates
        (choices (automaton.accepting.toList.map fun state => invoke (.state state))) input
        (.success input) := by
      simpa [accepted] using stateChoices
    have consumeRank :
        nameRank (.consumeAll : Name stateCount workLabelCount degree radius) <
          nameRank (.accepts : Name stateCount workLabelCount degree radius) := by
      simp [nameRank]
    have consumeEvaluation := recurse .consumeAll input
      (nameMeasure_lt_of_rank_lt input consumeRank)
    have consumeSuccess : (G automaton).Evaluates
        (invoke (.consumeAll : Name stateCount workLabelCount degree radius)) input
        (.success []) := by
      simpa [nameResult] using consumeEvaluation
    unfold acceptsRule
    simpa [nameResult, current, accepted] using
      (PegGrammar.Evaluates.sequenceSuccess stateChoicesSuccess consumeSuccess)
  · have stateChoicesFailure : (G automaton).Evaluates
        (choices (automaton.accepting.toList.map fun state => invoke (.state state))) input
        .failure := by
      simpa [accepted] using stateChoices
    unfold acceptsRule
    simpa [nameResult, current, accepted] using
      (PegGrammar.Evaluates.sequenceFailure stateChoicesFailure)

end Evaluation

end

end PegSeparation.SCAToPEG
