import PegSeparation.Common.Recognition
import PegSeparation.External.PartialTotalization.TotalityHelpers


namespace PegSeparation.Closure

open PegSeparation


def mapExpr {Terminal : Type} {sourceCount targetCount : Nat}
    (embed : Fin sourceCount → Fin targetCount) :
    ParsingExpression Terminal sourceCount → ParsingExpression Terminal targetCount
  | .empty => .empty
  | .failure => .failure
  | .terminal symbol => .terminal symbol
  | .nonterminal name => .nonterminal (embed name)
  | .sequence left right => .sequence (mapExpr embed left) (mapExpr embed right)
  | .orderedChoice left right => .orderedChoice (mapExpr embed left) (mapExpr embed right)
  | .notPredicate body => .notPredicate (mapExpr embed body)
  | .andPredicate body => .andPredicate (mapExpr embed body)

section Renaming

variable {Terminal : Type} [DecidableEq Terminal] {sourceCount targetCount : Nat}
  {source : PegGrammar Terminal sourceCount} {target : PegGrammar Terminal targetCount}
  {embed : Fin sourceCount → Fin targetCount}

theorem evaluates_mapExpr
    (ruleAgrees : ∀ name, target.rule (embed name) = mapExpr embed (source.rule name))
    {expression : ParsingExpression Terminal sourceCount}
    {input : List Terminal} {result : ParseResult Terminal}
    (evaluation : source.Evaluates expression input result) :
    target.Evaluates (mapExpr embed expression) input result := by
  induction evaluation with
  | empty input => exact .empty input
  | failure input => exact .failure input
  | terminal symbol input => exact .terminal symbol input
  | nonterminal _ ih =>
      refine .nonterminal ?_
      rw [ruleAgrees]
      exact ih
  | sequenceFailure _ ih => exact .sequenceFailure ih
  | sequenceSuccess _ _ ihLeft ihRight => exact .sequenceSuccess ihLeft ihRight
  | choiceLeft _ ih => exact .choiceLeft ih
  | choiceRight _ _ ihLeft ihRight => exact .choiceRight ihLeft ihRight
  | notSuccess _ ih => exact .notSuccess ih
  | notFailure _ ih => exact .notFailure ih
  | andSuccess _ ih => exact .andSuccess ih
  | andFailure _ ih => exact .andFailure ih

theorem evaluates_of_mapExpr
    (ruleAgrees : ∀ name, target.rule (embed name) = mapExpr embed (source.rule name))
    (sourceTotal : source.IsLoffTotal)
    {expression : ParsingExpression Terminal sourceCount}
    {input : List Terminal} {result : ParseResult Terminal}
    (evaluation : target.Evaluates (mapExpr embed expression) input result) :
    source.Evaluates expression input result := by
  obtain ⟨candidate, candidateEvaluation⟩ := sourceTotal expression input
  have transported := evaluates_mapExpr ruleAgrees candidateEvaluation
  have same :=
    External.LoffForwardRepaired.PegGrammar.evaluates_deterministic transported evaluation
  exact same ▸ candidateEvaluation

theorem evaluates_mapExpr_iff
    (ruleAgrees : ∀ name, target.rule (embed name) = mapExpr embed (source.rule name))
    (sourceTotal : source.IsLoffTotal)
    (expression : ParsingExpression Terminal sourceCount)
    (input : List Terminal) (result : ParseResult Terminal) :
    source.Evaluates expression input result ↔
      target.Evaluates (mapExpr embed expression) input result :=
  ⟨evaluates_mapExpr ruleAgrees, evaluates_of_mapExpr ruleAgrees sourceTotal⟩

end Renaming


def anyOf {Terminal : Type} {nonterminalCount : Nat} :
    List Terminal → ParsingExpression Terminal nonterminalCount
  | [] => .failure
  | symbol :: rest => .orderedChoice (.terminal symbol) (anyOf rest)

noncomputable def anyChar (Terminal : Type) [Fintype Terminal] (nonterminalCount : Nat) :
    ParsingExpression Terminal nonterminalCount :=
  anyOf (Finset.univ : Finset Terminal).toList

noncomputable def endOfInput (Terminal : Type) [Fintype Terminal] (nonterminalCount : Nat) :
    ParsingExpression Terminal nonterminalCount :=
  .notPredicate (anyChar Terminal nonterminalCount)

section AnyChar

variable {Terminal : Type} [DecidableEq Terminal] {nonterminalCount : Nat}
  (grammar : PegGrammar Terminal nonterminalCount)

theorem evaluates_anyOf_nil (symbols : List Terminal) :
    grammar.Evaluates (anyOf symbols) [] .failure := by
  induction symbols with
  | nil => exact .failure []
  | cons symbol _ ih => exact .choiceRight (.terminal symbol []) ih

theorem evaluates_anyOf_cons {symbols : List Terminal} {head : Terminal}
    (mem : head ∈ symbols) (tail : List Terminal) :
    grammar.Evaluates (anyOf symbols) (head :: tail) (.success tail) := by
  induction symbols with
  | nil => exact absurd mem (by simp)
  | cons symbol rest ih =>
      by_cases isHead : head = symbol
      · subst isHead
        refine .choiceLeft ?_
        have matched : PegGrammar.terminalResult head (head :: tail) = .success tail := by
          simp [PegGrammar.terminalResult]
        exact matched ▸ .terminal head (head :: tail)
      · have inRest : head ∈ rest := by
          rcases List.mem_cons.mp mem with same | inRest
          · exact absurd same isHead
          · exact inRest
        refine .choiceRight ?_ (ih inRest)
        have missed : PegGrammar.terminalResult symbol (head :: tail) = .failure := by
          simp [PegGrammar.terminalResult, isHead]
        exact missed ▸ .terminal symbol (head :: tail)

variable [Fintype Terminal]

theorem evaluates_endOfInput_nil :
    grammar.Evaluates (endOfInput Terminal nonterminalCount) [] (.success []) :=
  .notSuccess (evaluates_anyOf_nil grammar _)

theorem evaluates_endOfInput_cons (head : Terminal) (tail : List Terminal) :
    grammar.Evaluates (endOfInput Terminal nonterminalCount) (head :: tail) .failure :=
  .notFailure (evaluates_anyOf_cons grammar (by simp) tail)

end AnyChar


section Combined

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
  {leftCount rightCount : Nat}

def embedLeft (leftCount rightCount : Nat) :
    Fin leftCount → Fin (leftCount + rightCount + 1) :=
  fun name => (Fin.castAdd rightCount name).castSucc

def embedRight (leftCount rightCount : Nat) :
    Fin rightCount → Fin (leftCount + rightCount + 1) :=
  fun name => (Fin.natAdd leftCount name).castSucc

def combined (left : PegGrammar Terminal leftCount) (right : PegGrammar Terminal rightCount)
    (startRule : ParsingExpression Terminal (leftCount + rightCount + 1)) :
    PegGrammar Terminal (leftCount + rightCount + 1) where
  rule :=
    Fin.lastCases startRule
      (Fin.addCases
        (fun name => mapExpr (embedLeft leftCount rightCount) (left.rule name))
        (fun name => mapExpr (embedRight leftCount rightCount) (right.rule name)))
  start := Fin.last (leftCount + rightCount)

variable {left : PegGrammar Terminal leftCount} {right : PegGrammar Terminal rightCount}
  {startRule : ParsingExpression Terminal (leftCount + rightCount + 1)}

omit [Fintype Terminal] [DecidableEq Terminal] in
@[simp] theorem combined_start :
    (combined left right startRule).start = Fin.last (leftCount + rightCount) :=
  rfl

omit [Fintype Terminal] [DecidableEq Terminal] in
@[simp] theorem combined_rule_last :
    (combined left right startRule).rule (Fin.last (leftCount + rightCount)) = startRule := by
  simp only [combined, Fin.lastCases_last]

omit [Fintype Terminal] [DecidableEq Terminal] in
@[simp] theorem combined_rule_embedLeft (name : Fin leftCount) :
    (combined left right startRule).rule (embedLeft leftCount rightCount name) =
      mapExpr (embedLeft leftCount rightCount) (left.rule name) := by
  simp only [combined, embedLeft, Fin.lastCases_castSucc, Fin.addCases_left]

omit [Fintype Terminal] [DecidableEq Terminal] in
@[simp] theorem combined_rule_embedRight (name : Fin rightCount) :
    (combined left right startRule).rule (embedRight leftCount rightCount name) =
      mapExpr (embedRight leftCount rightCount) (right.rule name) := by
  simp only [combined, embedRight, Fin.lastCases_castSucc, Fin.addCases_right]


noncomputable def checkLeft (left : PegGrammar Terminal leftCount) (rightCount : Nat) :
    ParsingExpression Terminal (leftCount + rightCount + 1) :=
  .sequence (.nonterminal (embedLeft leftCount rightCount left.start))
    (endOfInput Terminal (leftCount + rightCount + 1))

noncomputable def checkRight (leftCount : Nat) (right : PegGrammar Terminal rightCount) :
    ParsingExpression Terminal (leftCount + rightCount + 1) :=
  .sequence (.nonterminal (embedRight leftCount rightCount right.start))
    (endOfInput Terminal (leftCount + rightCount + 1))

theorem evaluates_checkLeft_of_recognizes {input : List Terminal}
    (recognized : left.Recognizes input) :
    (combined left right startRule).Evaluates (checkLeft left rightCount) input (.success []) := by
  have transported :
      (combined left right startRule).Evaluates
        (mapExpr (embedLeft leftCount rightCount) (.nonterminal left.start))
        input (.success []) :=
    evaluates_mapExpr (fun name => combined_rule_embedLeft name) recognized
  exact .sequenceSuccess transported (evaluates_endOfInput_nil _)

theorem evaluates_checkRight_of_recognizes {input : List Terminal}
    (recognized : right.Recognizes input) :
    (combined left right startRule).Evaluates (checkRight leftCount right) input
      (.success []) := by
  have transported :
      (combined left right startRule).Evaluates
        (mapExpr (embedRight leftCount rightCount) (.nonterminal right.start))
        input (.success []) :=
    evaluates_mapExpr (fun name => combined_rule_embedRight name) recognized
  exact .sequenceSuccess transported (evaluates_endOfInput_nil _)

theorem evaluates_checkLeft_of_not_recognizes (leftTotal : left.IsLoffTotal)
    {input : List Terminal} (notRecognized : ¬ left.Recognizes input) :
    (combined left right startRule).Evaluates (checkLeft left rightCount) input .failure := by
  obtain ⟨result, evaluation⟩ := leftTotal (.nonterminal left.start) input
  have transported :
      (combined left right startRule).Evaluates
        (mapExpr (embedLeft leftCount rightCount) (.nonterminal left.start)) input result :=
    evaluates_mapExpr (fun name => combined_rule_embedLeft name) evaluation
  match result with
  | .failure => exact .sequenceFailure transported
  | .success [] => exact absurd evaluation notRecognized
  | .success (head :: tail) =>
      exact .sequenceSuccess transported (evaluates_endOfInput_cons _ head tail)

theorem evaluates_checkRight_of_not_recognizes (rightTotal : right.IsLoffTotal)
    {input : List Terminal} (notRecognized : ¬ right.Recognizes input) :
    (combined left right startRule).Evaluates (checkRight leftCount right) input .failure := by
  obtain ⟨result, evaluation⟩ := rightTotal (.nonterminal right.start) input
  have transported :
      (combined left right startRule).Evaluates
        (mapExpr (embedRight leftCount rightCount) (.nonterminal right.start)) input result :=
    evaluates_mapExpr (fun name => combined_rule_embedRight name) evaluation
  match result with
  | .failure => exact .sequenceFailure transported
  | .success [] => exact absurd evaluation notRecognized
  | .success (head :: tail) =>
      exact .sequenceSuccess transported (evaluates_endOfInput_cons _ head tail)

theorem checkLeft_total (leftTotal : left.IsLoffTotal) (input : List Terminal) :
    ∃ result,
      (combined left right startRule).Evaluates (checkLeft left rightCount) input result := by
  by_cases recognized : left.Recognizes input
  · exact ⟨_, evaluates_checkLeft_of_recognizes recognized⟩
  · exact ⟨_, evaluates_checkLeft_of_not_recognizes leftTotal recognized⟩

theorem checkRight_total (rightTotal : right.IsLoffTotal) (input : List Terminal) :
    ∃ result,
      (combined left right startRule).Evaluates (checkRight leftCount right) input result := by
  by_cases recognized : right.Recognizes input
  · exact ⟨_, evaluates_checkRight_of_recognizes recognized⟩
  · exact ⟨_, evaluates_checkRight_of_not_recognizes rightTotal recognized⟩


omit [Fintype Terminal] in
theorem combined_isLoffTotal (leftTotal : left.IsLoffTotal) (rightTotal : right.IsLoffTotal)
    (startTotal : ∀ input : List Terminal,
      ∃ result, (combined left right startRule).Evaluates startRule input result) :
    (combined left right startRule).IsLoffTotal := by
  apply PegGrammar.PartialTotalityHelpers.loffTotal_of_nonterminal_total
  intro name input
  induction name using Fin.lastCases with
  | last =>
      obtain ⟨result, evaluation⟩ := startTotal input
      exact ⟨result, .nonterminal (by rw [combined_rule_last]; exact evaluation)⟩
  | cast inner =>
      induction inner using Fin.addCases with
      | left name =>
          change ∃ result, (combined left right startRule).Evaluates
            (.nonterminal (embedLeft leftCount rightCount name)) input result
          obtain ⟨result, evaluation⟩ := leftTotal (left.rule name) input
          exact ⟨result, .nonterminal (by
            rw [combined_rule_embedLeft]
            exact evaluates_mapExpr (fun other => combined_rule_embedLeft other) evaluation)⟩
      | right name =>
          change ∃ result, (combined left right startRule).Evaluates
            (.nonterminal (embedRight leftCount rightCount name)) input result
          obtain ⟨result, evaluation⟩ := rightTotal (right.rule name) input
          exact ⟨result, .nonterminal (by
            rw [combined_rule_embedRight]
            exact evaluates_mapExpr (fun other => combined_rule_embedRight other) evaluation)⟩

omit [Fintype Terminal] in
theorem combined_recognizes_iff (input : List Terminal) :
    (combined left right startRule).Recognizes input ↔
      (combined left right startRule).Evaluates startRule input (.success []) := by
  constructor
  · intro recognized
    rw [PegGrammar.Recognizes, combined_start] at recognized
    cases recognized with
    | nonterminal body => rwa [combined_rule_last] at body
  · intro evaluation
    rw [PegGrammar.Recognizes, combined_start]
    exact .nonterminal (by rw [combined_rule_last]; exact evaluation)


noncomputable def unionStart (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount) :
    ParsingExpression Terminal (leftCount + rightCount + 1) :=
  .orderedChoice (checkLeft left rightCount) (checkRight leftCount right)

theorem unionStart_total (leftTotal : left.IsLoffTotal) (rightTotal : right.IsLoffTotal)
    (input : List Terminal) :
    ∃ result,
      (combined left right (unionStart left right)).Evaluates (unionStart left right) input
        result :=
  PegGrammar.PartialTotalityHelpers.orderedChoice_total (checkLeft_total leftTotal input)
    (checkRight_total rightTotal input)

theorem combined_union_recognizes_iff (leftTotal : left.IsLoffTotal)
    (rightTotal : right.IsLoffTotal) (input : List Terminal) :
    (combined left right (unionStart left right)).Recognizes input ↔
      (left.Recognizes input ∨ right.Recognizes input) := by
  rw [combined_recognizes_iff]
  constructor
  · intro evaluation
    by_contra notEither
    push Not at notEither
    obtain ⟨notLeft, notRight⟩ := notEither
    have fails :
        (combined left right (unionStart left right)).Evaluates (unionStart left right) input
          .failure :=
      .choiceRight (evaluates_checkLeft_of_not_recognizes leftTotal notLeft)
        (evaluates_checkRight_of_not_recognizes rightTotal notRight)
    exact absurd
      (External.LoffForwardRepaired.PegGrammar.evaluates_deterministic fails evaluation)
      (by simp)
  · intro either
    by_cases recognizedLeft : left.Recognizes input
    · exact .choiceLeft (evaluates_checkLeft_of_recognizes recognizedLeft)
    · have recognizedRight : right.Recognizes input := either.resolve_left recognizedLeft
      exact .choiceRight (evaluates_checkLeft_of_not_recognizes leftTotal recognizedLeft)
        (evaluates_checkRight_of_recognizes recognizedRight)


noncomputable def interStart (left : PegGrammar Terminal leftCount)
    (right : PegGrammar Terminal rightCount) :
    ParsingExpression Terminal (leftCount + rightCount + 1) :=
  .sequence (.andPredicate (checkLeft left rightCount)) (checkRight leftCount right)

theorem interStart_total (leftTotal : left.IsLoffTotal) (rightTotal : right.IsLoffTotal)
    (input : List Terminal) :
    ∃ result,
      (combined left right (interStart left right)).Evaluates (interStart left right) input
        result :=
  PegGrammar.PartialTotalityHelpers.sequence_total
    (PegGrammar.PartialTotalityHelpers.andPredicate_total (checkLeft_total leftTotal input))
    (fun middle => checkRight_total rightTotal middle)

theorem combined_inter_recognizes_iff (leftTotal : left.IsLoffTotal)
    (rightTotal : right.IsLoffTotal) (input : List Terminal) :
    (combined left right (interStart left right)).Recognizes input ↔
      (left.Recognizes input ∧ right.Recognizes input) := by
  rw [combined_recognizes_iff]
  constructor
  · intro evaluation
    by_contra notBoth
    have fails :
        (combined left right (interStart left right)).Evaluates (interStart left right) input
          .failure := by
      by_cases recognizedLeft : left.Recognizes input
      · have notRight : ¬ right.Recognizes input := fun h => notBoth ⟨recognizedLeft, h⟩
        exact .sequenceSuccess
          (.andSuccess (evaluates_checkLeft_of_recognizes recognizedLeft))
          (evaluates_checkRight_of_not_recognizes rightTotal notRight)
      · exact .sequenceFailure
          (.andFailure (evaluates_checkLeft_of_not_recognizes leftTotal recognizedLeft))
    exact absurd
      (External.LoffForwardRepaired.PegGrammar.evaluates_deterministic fails evaluation)
      (by simp)
  · rintro ⟨recognizedLeft, recognizedRight⟩
    exact .sequenceSuccess (.andSuccess (evaluates_checkLeft_of_recognizes recognizedLeft))
      (evaluates_checkRight_of_recognizes recognizedRight)

end Combined


set_option linter.unusedFintypeInType false in
theorem recognizedByTotalPEG_union {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    {L₁ L₂ : Language Terminal} (h₁ : PegSeparation.RecognizedByTotalPEG L₁)
    (h₂ : PegSeparation.RecognizedByTotalPEG L₂) :
    PegSeparation.RecognizedByTotalPEG (L₁ + L₂) := by
  obtain ⟨leftCount, left, leftTotal, leftCorrect⟩ := h₁
  obtain ⟨rightCount, right, rightTotal, rightCorrect⟩ := h₂
  refine ⟨leftCount + rightCount + 1, combined left right (unionStart left right), ?_, ?_⟩
  · exact combined_isLoffTotal leftTotal rightTotal (unionStart_total leftTotal rightTotal)
  · intro input
    rw [combined_union_recognizes_iff leftTotal rightTotal, leftCorrect, rightCorrect]
    exact Iff.rfl

set_option linter.unusedFintypeInType false in
theorem recognizedByTotalPEG_inter {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    {L₁ L₂ : Language Terminal} (h₁ : PegSeparation.RecognizedByTotalPEG L₁)
    (h₂ : PegSeparation.RecognizedByTotalPEG L₂) :
    PegSeparation.RecognizedByTotalPEG (L₁ ⊓ L₂) := by
  obtain ⟨leftCount, left, leftTotal, leftCorrect⟩ := h₁
  obtain ⟨rightCount, right, rightTotal, rightCorrect⟩ := h₂
  refine ⟨leftCount + rightCount + 1, combined left right (interStart left right), ?_, ?_⟩
  · exact combined_isLoffTotal leftTotal rightTotal (interStart_total leftTotal rightTotal)
  · intro input
    rw [combined_inter_recognizes_iff leftTotal rightTotal, leftCorrect, rightCorrect]
    exact Iff.rfl

end PegSeparation.Closure
