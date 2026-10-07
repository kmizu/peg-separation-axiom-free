import PegSeparation.Closure.HomomorphismInternalSentinel


namespace PegSeparation.Closure

open PegSeparation

namespace HomomorphismInternal

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
  {leftCount rightCount : Nat}

def MarkedProduct
    (left right : Language Terminal) :
    Language (Option Terminal) := fun input =>
  ∃ before,
    before ∈ left ∧
      ∃ after,
        after ∈ right ∧
          input = liftWord before ++ none :: liftWord after

def markedProductStart
    (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount) :
    ParsingExpression (Option Terminal) (leftCount + rightCount + 1) :=
  .sequence
    (.nonterminal (embedLeft leftCount rightCount left.start))
    (.sequence
      (.terminal none)
      (.nonterminal (embedRight leftCount rightCount right.start)))

def markedProductGrammar
    (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount) :
    PegGrammar (Option Terminal) (leftCount + rightCount + 1) :=
  combined (liftGrammar left) (liftGrammar right)
    (markedProductStart left right)

@[simp] theorem markedProductGrammar_start
    (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount) :
    (markedProductGrammar left right).start =
      Fin.last (leftCount + rightCount) :=
  rfl

@[simp] theorem markedProductGrammar_rule_left
    (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount)
    (name : Fin leftCount) :
    (markedProductGrammar left right).rule
        (embedLeft leftCount rightCount name) =
      mapExpr (embedLeft leftCount rightCount)
        ((liftGrammar left).rule name) := by
  simp [markedProductGrammar]

@[simp] theorem markedProductGrammar_rule_right
    (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount)
    (name : Fin rightCount) :
    (markedProductGrammar left right).rule
        (embedRight leftCount rightCount name) =
      mapExpr (embedRight leftCount rightCount)
        ((liftGrammar right).rule name) := by
  simp [markedProductGrammar]

@[simp] theorem markedProductGrammar_rule_start
    (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount) :
    (markedProductGrammar left right).rule
        (Fin.last (leftCount + rightCount)) =
      markedProductStart left right := by
  simp [markedProductGrammar]

theorem evaluates_marked_left
    (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount)
    {expression : ParsingExpression (Option Terminal) leftCount}
    {input : List (Option Terminal)}
    {result : ParseResult (Option Terminal)}
    (evaluation : (liftGrammar left).Evaluates expression input result) :
    (markedProductGrammar left right).Evaluates
      (mapExpr (embedLeft leftCount rightCount) expression) input result :=
  evaluates_mapExpr
    (fun name => markedProductGrammar_rule_left left right name)
    evaluation

theorem evaluates_marked_right
    (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount)
    {expression : ParsingExpression (Option Terminal) rightCount}
    {input : List (Option Terminal)}
    {result : ParseResult (Option Terminal)}
    (evaluation : (liftGrammar right).Evaluates expression input result) :
    (markedProductGrammar left right).Evaluates
      (mapExpr (embedRight leftCount rightCount) expression) input result :=
  evaluates_mapExpr
    (fun name => markedProductGrammar_rule_right left right name)
    evaluation

theorem evaluates_of_marked_left
    (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount)
    (leftTotal : left.IsLoffTotal)
    {expression : ParsingExpression (Option Terminal) leftCount}
    {input : List (Option Terminal)}
    {result : ParseResult (Option Terminal)}
    (evaluation :
      (markedProductGrammar left right).Evaluates
        (mapExpr (embedLeft leftCount rightCount) expression) input result) :
    (liftGrammar left).Evaluates expression input result :=
  evaluates_of_mapExpr
    (fun name => markedProductGrammar_rule_left left right name)
    (liftGrammar_isLoffTotal left leftTotal) evaluation

theorem evaluates_of_marked_right
    (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount)
    (rightTotal : right.IsLoffTotal)
    {expression : ParsingExpression (Option Terminal) rightCount}
    {input : List (Option Terminal)}
    {result : ParseResult (Option Terminal)}
    (evaluation :
      (markedProductGrammar left right).Evaluates
        (mapExpr (embedRight leftCount rightCount) expression) input result) :
    (liftGrammar right).Evaluates expression input result :=
  evaluates_of_mapExpr
    (fun name => markedProductGrammar_rule_right left right name)
    (liftGrammar_isLoffTotal right rightTotal) evaluation

theorem markedProductStart_total
    (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount)
    (leftTotal : left.IsLoffTotal)
    (rightTotal : right.IsLoffTotal)
    (input : List (Option Terminal)) :
    ∃ result,
      (markedProductGrammar left right).Evaluates
        (markedProductStart left right) input result := by
  apply PegGrammar.PartialTotalityHelpers.sequence_total
  · obtain ⟨result, evaluation⟩ :=
      liftGrammar_isLoffTotal left leftTotal
        (.nonterminal (liftGrammar left).start) input
    exact ⟨result, evaluates_marked_left left right evaluation⟩
  · intro middle
    apply PegGrammar.PartialTotalityHelpers.sequence_total
    · exact ⟨PegGrammar.terminalResult none middle, .terminal none middle⟩
    · intro after
      obtain ⟨result, evaluation⟩ :=
        liftGrammar_isLoffTotal right rightTotal
          (.nonterminal (liftGrammar right).start) after
      exact ⟨result, evaluates_marked_right left right evaluation⟩

theorem markedProductGrammar_isLoffTotal
    (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount)
    (leftTotal : left.IsLoffTotal)
    (rightTotal : right.IsLoffTotal) :
    (markedProductGrammar left right).IsLoffTotal :=
  combined_isLoffTotal
    (liftGrammar_isLoffTotal left leftTotal)
    (liftGrammar_isLoffTotal right rightTotal)
    (markedProductStart_total left right leftTotal rightTotal)

private theorem exists_middle_of_sequence_success
    {count : Nat}
    {grammar : PegGrammar (Option Terminal) count}
    {left right : ParsingExpression (Option Terminal) count}
    {input remaining : List (Option Terminal)}
    (evaluation :
      grammar.Evaluates (.sequence left right) input (.success remaining)) :
    ∃ middle,
      grammar.Evaluates left input (.success middle) ∧
        grammar.Evaluates right middle (.success remaining) := by
  cases evaluation with
  | sequenceSuccess leftEvaluation rightEvaluation =>
      exact ⟨_, leftEvaluation, rightEvaluation⟩

private theorem evaluates_terminal_none_success_iff
    {count : Nat}
    (grammar : PegGrammar (Option Terminal) count)
    (input remaining : List (Option Terminal)) :
    grammar.Evaluates (.terminal none) input (.success remaining) ↔
      input = none :: remaining := by
  constructor
  · intro evaluation
    have canonical :
        grammar.Evaluates (.terminal none) input
          (PegGrammar.terminalResult none input) :=
      .terminal none input
    have same :=
      PegSeparation.External.LoffForwardRepaired.PegGrammar.evaluates_deterministic
        evaluation canonical
    cases input with
    | nil =>
        simp [PegGrammar.terminalResult] at same
    | cons head tail =>
        cases head with
        | none =>
            simp [PegGrammar.terminalResult] at same
            cases same
            rfl
        | some symbol =>
            simp [PegGrammar.terminalResult] at same
  · rintro rfl
    simpa [PegGrammar.terminalResult] using
      (PegGrammar.Evaluates.terminal (grammar := grammar) none
        (none :: remaining))

theorem markedProductGrammar_recognizes_iff
    (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount)
    (leftTotal : left.IsLoffTotal)
    (rightTotal : right.IsLoffTotal)
    (leftLanguage rightLanguage : Language Terminal)
    (leftCorrect :
      ∀ input, left.Recognizes input ↔ input ∈ leftLanguage)
    (rightCorrect :
      ∀ input, right.Recognizes input ↔ input ∈ rightLanguage)
    (input : List (Option Terminal)) :
    (markedProductGrammar left right).Recognizes input ↔
      input ∈ MarkedProduct leftLanguage rightLanguage := by
  change
    (combined (liftGrammar left) (liftGrammar right)
      (markedProductStart left right)).Recognizes input ↔ _
  rw [combined_recognizes_iff]
  constructor
  · intro evaluation
    obtain ⟨middle, leftEvaluation, restEvaluation⟩ :=
      exists_middle_of_sequence_success evaluation
    obtain ⟨after, sentinelEvaluation, rightEvaluation⟩ :=
      exists_middle_of_sequence_success restEvaluation
    have middleEq :
        middle = none :: after :=
      (evaluates_terminal_none_success_iff
        (markedProductGrammar left right) middle after).mp
        sentinelEvaluation
    subst middle
    have liftedLeft :
        (liftGrammar left).Evaluates
          (.nonterminal left.start) input (.success (none :: after)) :=
      evaluates_of_marked_left left right leftTotal leftEvaluation
    obtain ⟨before, inputEq, beforeEvaluation⟩ :=
      (evaluates_liftExpr_to_sentinel_iff left leftTotal
        (.nonterminal left.start) input after).mp liftedLeft
    have liftedRight :
        (liftGrammar right).Recognizes after :=
      evaluates_of_marked_right left right rightTotal rightEvaluation
    obtain ⟨afterWord, afterMember, afterEq⟩ :=
      (liftGrammar_recognizes_iff right rightTotal rightLanguage
        rightCorrect after).mp liftedRight
    refine ⟨before, (leftCorrect before).mp beforeEvaluation,
      afterWord, afterMember, ?_⟩
    rw [inputEq, afterEq]
  · rintro ⟨before, beforeMember, after, afterMember, rfl⟩
    have beforeEvaluation :
        left.Evaluates (.nonterminal left.start) before (.success []) :=
      (leftCorrect before).mpr beforeMember
    have liftedLeft :
        (liftGrammar left).Evaluates (.nonterminal left.start)
          (liftWord before ++ none :: liftWord after)
          (.success (none :: liftWord after)) := by
      simpa [liftExpr] using
        evaluates_liftExpr_with_blocked left (none :: liftWord after)
          (Or.inr ⟨liftWord after, rfl⟩) beforeEvaluation
    have markedLeft :=
      evaluates_marked_left left right liftedLeft
    have liftedRight :
        (liftGrammar right).Recognizes (liftWord after) :=
      (liftGrammar_recognizes_iff right rightTotal rightLanguage
        rightCorrect (liftWord after)).mpr
        ⟨after, afterMember, rfl⟩
    have markedRight :=
      evaluates_marked_right left right liftedRight
    have sentinelEvaluation :
        (markedProductGrammar left right).Evaluates (.terminal none)
          (none :: liftWord after) (.success (liftWord after)) := by
      simpa [PegGrammar.terminalResult] using
        (PegGrammar.Evaluates.terminal
          (grammar := markedProductGrammar left right) none
          (none :: liftWord after))
    exact .sequenceSuccess markedLeft
      (.sequenceSuccess sentinelEvaluation markedRight)

theorem recognizedByTotalPEG_markedProduct
    {leftLanguage rightLanguage : Language Terminal}
    (leftRecognized : RecognizedByTotalPEG leftLanguage)
    (rightRecognized : RecognizedByTotalPEG rightLanguage) :
    RecognizedByTotalPEG
      (MarkedProduct leftLanguage rightLanguage) := by
  obtain ⟨leftCount, left, leftTotal, leftCorrect⟩ := leftRecognized
  obtain ⟨rightCount, right, rightTotal, rightCorrect⟩ := rightRecognized
  exact ⟨leftCount + rightCount + 1,
    markedProductGrammar left right,
    markedProductGrammar_isLoffTotal left right leftTotal rightTotal,
    markedProductGrammar_recognizes_iff left right leftTotal rightTotal
      leftLanguage rightLanguage leftCorrect rightCorrect⟩

end HomomorphismInternal

end PegSeparation.Closure
