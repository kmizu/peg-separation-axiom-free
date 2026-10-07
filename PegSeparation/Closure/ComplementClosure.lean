import PegSeparation.Closure.BooleanClosure


namespace PegSeparation.Closure

open PegSeparation


noncomputable def universalRule (Terminal : Type) [Fintype Terminal] :
    ParsingExpression Terminal 1 :=
  .orderedChoice
    (.sequence (anyChar Terminal 1) (.nonterminal 0))
    .empty

noncomputable def universalGrammar (Terminal : Type) [Fintype Terminal] :
    PegGrammar Terminal 1 where
  rule := fun _ => universalRule Terminal
  start := 0

@[simp] theorem universalGrammar_rule
    (Terminal : Type) [Fintype Terminal] (name : Fin 1) :
    (universalGrammar Terminal).rule name = universalRule Terminal :=
  rfl

@[simp] theorem universalGrammar_start
    (Terminal : Type) [Fintype Terminal] :
    (universalGrammar Terminal).start = 0 :=
  rfl

theorem universalGrammar_consumes
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    (input : List Terminal) :
    (universalGrammar Terminal).Evaluates
      (.nonterminal (universalGrammar Terminal).start) input (.success []) := by
  induction input with
  | nil =>
      refine PegGrammar.Evaluates.nonterminal ?_
      rw [universalGrammar_rule]
      exact .choiceRight
        (.sequenceFailure
          (by
            simpa [anyChar] using
              evaluates_anyOf_nil (universalGrammar Terminal)
                (Finset.univ : Finset Terminal).toList))
        (.empty [])
  | cons head tail ih =>
      refine PegGrammar.Evaluates.nonterminal ?_
      rw [universalGrammar_rule]
      refine .choiceLeft (.sequenceSuccess ?_ ih)
      simpa [anyChar] using
        evaluates_anyOf_cons (universalGrammar Terminal)
          (symbols := (Finset.univ : Finset Terminal).toList)
          (head := head) (by simp) tail

theorem universalGrammar_isLoffTotal
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal] :
    (universalGrammar Terminal).IsLoffTotal := by
  apply PegGrammar.PartialTotalityHelpers.loffTotal_of_nonterminal_total
  intro name input
  have hname : name = 0 := Fin.eq_zero name
  subst name
  exact ⟨.success [], universalGrammar_consumes input⟩

theorem universalGrammar_recognizes
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    (input : List Terminal) :
    (universalGrammar Terminal).Recognizes input :=
  universalGrammar_consumes input


section ComplementGrammar

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
  {leftCount rightCount : Nat}
  {left : PegGrammar Terminal leftCount}
  {right : PegGrammar Terminal rightCount}

noncomputable def complementStart
    (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount) :
    ParsingExpression Terminal (leftCount + rightCount + 1) :=
  .sequence
    (.notPredicate (checkLeft left rightCount))
    (checkRight leftCount right)

theorem complementStart_total
    (leftTotal : left.IsLoffTotal)
    (rightTotal : right.IsLoffTotal)
    (input : List Terminal) :
    ∃ result,
      (combined left right (complementStart left right)).Evaluates
        (complementStart left right) input result :=
  PegGrammar.PartialTotalityHelpers.sequence_total
    (PegGrammar.PartialTotalityHelpers.notPredicate_total
      (checkLeft_total leftTotal input))
    (fun middle => checkRight_total rightTotal middle)

theorem combined_complement_recognizes_iff
    (leftTotal : left.IsLoffTotal)
    (rightTotal : right.IsLoffTotal)
    (input : List Terminal) :
    (combined left right (complementStart left right)).Recognizes input ↔
      (¬ left.Recognizes input) ∧ right.Recognizes input := by
  rw [combined_recognizes_iff]
  constructor
  · intro evaluation
    constructor
    · intro recognizedLeft
      have fails :
          (combined left right (complementStart left right)).Evaluates
            (complementStart left right) input .failure :=
        .sequenceFailure
          (.notFailure (evaluates_checkLeft_of_recognizes recognizedLeft))
      exact absurd
        (External.LoffForwardRepaired.PegGrammar.evaluates_deterministic
          fails evaluation)
        (by simp)
    · by_contra notRecognizedRight
      by_cases recognizedLeft : left.Recognizes input
      · have fails :
            (combined left right (complementStart left right)).Evaluates
              (complementStart left right) input .failure :=
          .sequenceFailure
            (.notFailure (evaluates_checkLeft_of_recognizes recognizedLeft))
        exact absurd
          (External.LoffForwardRepaired.PegGrammar.evaluates_deterministic
            fails evaluation)
          (by simp)
      · have fails :
            (combined left right (complementStart left right)).Evaluates
              (complementStart left right) input .failure :=
          .sequenceSuccess
            (.notSuccess
              (evaluates_checkLeft_of_not_recognizes
                leftTotal recognizedLeft))
            (evaluates_checkRight_of_not_recognizes
              rightTotal notRecognizedRight)
        exact absurd
          (External.LoffForwardRepaired.PegGrammar.evaluates_deterministic
            fails evaluation)
          (by simp)
  · rintro ⟨notRecognizedLeft, recognizedRight⟩
    exact .sequenceSuccess
      (.notSuccess
        (evaluates_checkLeft_of_not_recognizes
          leftTotal notRecognizedLeft))
      (evaluates_checkRight_of_recognizes recognizedRight)

end ComplementGrammar


set_option linter.unusedFintypeInType false in
theorem recognizedByTotalPEG_compl
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    {L : Language Terminal}
    (h : PegSeparation.RecognizedByTotalPEG L) :
    PegSeparation.RecognizedByTotalPEG Lᶜ := by
  obtain ⟨leftCount, left, leftTotal, leftCorrect⟩ := h
  let right := universalGrammar Terminal
  have rightTotal : right.IsLoffTotal :=
    universalGrammar_isLoffTotal
  refine
    ⟨leftCount + 1 + 1,
      combined left right (complementStart left right),
      combined_isLoffTotal leftTotal rightTotal
        (complementStart_total leftTotal rightTotal),
      ?_⟩
  intro input
  rw [combined_complement_recognizes_iff leftTotal rightTotal]
  rw [leftCorrect]
  constructor
  · rintro ⟨notMember, -⟩
    exact notMember
  · intro notMember
    exact ⟨notMember, universalGrammar_recognizes input⟩

end PegSeparation.Closure
