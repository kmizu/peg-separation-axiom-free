import PegSeparation.Closure.BooleanClosure


namespace PegSeparation.Closure

open PegSeparation

namespace HomomorphismInternal

variable {Terminal : Type} [DecidableEq Terminal]
  {nonterminalCount : Nat}

def liftWord (word : List Terminal) : List (Option Terminal) :=
  word.map some

@[simp] theorem liftWord_nil :
    liftWord ([] : List Terminal) = [] :=
  rfl

@[simp] theorem liftWord_cons (symbol : Terminal) (word : List Terminal) :
    liftWord (symbol :: word) = some symbol :: liftWord word :=
  rfl

@[simp] theorem liftWord_append (left right : List Terminal) :
    liftWord (left ++ right) = liftWord left ++ liftWord right := by
  simp [liftWord]

@[simp] theorem liftWord_eq_nil_iff (word : List Terminal) :
    liftWord word = [] ↔ word = [] := by
  simp [liftWord]

def liftExpr :
    ParsingExpression Terminal nonterminalCount →
      ParsingExpression (Option Terminal) nonterminalCount
  | .empty => .empty
  | .failure => .failure
  | .terminal symbol => .terminal (some symbol)
  | .nonterminal name => .nonterminal name
  | .sequence left right => .sequence (liftExpr left) (liftExpr right)
  | .orderedChoice left right =>
      .orderedChoice (liftExpr left) (liftExpr right)
  | .notPredicate body => .notPredicate (liftExpr body)
  | .andPredicate body => .andPredicate (liftExpr body)

def liftGrammar
    (grammar : PegGrammar Terminal nonterminalCount) :
    PegGrammar (Option Terminal) nonterminalCount where
  rule name := liftExpr (grammar.rule name)
  start := grammar.start

@[simp] theorem liftGrammar_rule
    (grammar : PegGrammar Terminal nonterminalCount)
    (name : Fin nonterminalCount) :
    (liftGrammar grammar).rule name = liftExpr (grammar.rule name) :=
  rfl

@[simp] theorem liftGrammar_start
    (grammar : PegGrammar Terminal nonterminalCount) :
    (liftGrammar grammar).start = grammar.start :=
  rfl

def BlockedSuffix (suffix : List (Option Terminal)) : Prop :=
  suffix = [] ∨ ∃ tail, suffix = none :: tail

def liftResult (suffix : List (Option Terminal)) :
    ParseResult Terminal → ParseResult (Option Terminal)
  | .failure => .failure
  | .success remaining => .success (liftWord remaining ++ suffix)

@[simp] theorem liftResult_failure (suffix : List (Option Terminal)) :
    liftResult suffix (ParseResult.failure : ParseResult Terminal) =
      ParseResult.failure :=
  rfl

@[simp] theorem liftResult_success
    (suffix : List (Option Terminal)) (remaining : List Terminal) :
    liftResult suffix (.success remaining) =
      .success (liftWord remaining ++ suffix) :=
  rfl

theorem exists_liftWord_append_blocked
    (input : List (Option Terminal)) :
    ∃ oldInput suffix,
      input = liftWord oldInput ++ suffix ∧ BlockedSuffix suffix := by
  induction input with
  | nil =>
      exact ⟨[], [], rfl, Or.inl rfl⟩
  | cons head tail ih =>
      cases head with
      | none =>
          exact ⟨[], none :: tail, rfl, Or.inr ⟨tail, rfl⟩⟩
      | some symbol =>
          obtain ⟨oldInput, suffix, hinput, blocked⟩ := ih
          refine ⟨symbol :: oldInput, suffix, ?_, blocked⟩
          simp only [liftWord_cons, hinput, List.cons_append]

theorem evaluates_liftExpr_with_blocked
    (grammar : PegGrammar Terminal nonterminalCount)
    {expression : ParsingExpression Terminal nonterminalCount}
    {input : List Terminal}
    {result : ParseResult Terminal}
    (suffix : List (Option Terminal))
    (blocked : BlockedSuffix suffix)
    (evaluation : grammar.Evaluates expression input result) :
    (liftGrammar grammar).Evaluates (liftExpr expression)
      (liftWord input ++ suffix) (liftResult suffix result) := by
  induction evaluation with
  | empty input =>
      exact .empty _
  | failure input =>
      exact .failure _
  | terminal symbol input =>
      have terminalResultEq :
          PegGrammar.terminalResult (some symbol)
              (liftWord input ++ suffix) =
            liftResult suffix
              (PegGrammar.terminalResult symbol input) := by
        cases input with
        | nil =>
            rcases blocked with rfl | ⟨tail, rfl⟩
            · rfl
            · simp [PegGrammar.terminalResult]
        | cons actual rest =>
            by_cases same : actual = symbol
            · simp [PegGrammar.terminalResult, same]
            · simp [PegGrammar.terminalResult, same]
      exact terminalResultEq ▸ .terminal (some symbol) _
  | nonterminal body ih =>
      exact .nonterminal (by
        rw [liftGrammar_rule]
        exact ih)
  | sequenceFailure leftFails ih =>
      exact .sequenceFailure ih
  | sequenceSuccess leftSucceeds rightResult ihLeft ihRight =>
      exact .sequenceSuccess ihLeft ihRight
  | choiceLeft leftSucceeds ih =>
      exact .choiceLeft ih
  | choiceRight leftFails rightResult ihLeft ihRight =>
      exact .choiceRight ihLeft ihRight
  | notSuccess bodyFails ih =>
      exact .notSuccess ih
  | notFailure bodySucceeds ih =>
      exact .notFailure ih
  | andSuccess bodySucceeds ih =>
      exact .andSuccess ih
  | andFailure bodyFails ih =>
      exact .andFailure ih

theorem liftGrammar_isLoffTotal
    (grammar : PegGrammar Terminal nonterminalCount)
    (total : grammar.IsLoffTotal) :
    (liftGrammar grammar).IsLoffTotal := by
  apply PegGrammar.PartialTotalityHelpers.loffTotal_of_nonterminal_total
  intro name input
  obtain ⟨oldInput, suffix, hinput, blocked⟩ :=
    exists_liftWord_append_blocked input
  obtain ⟨result, evaluation⟩ := total (grammar.rule name) oldInput
  refine ⟨liftResult suffix result, .nonterminal ?_⟩
  rw [liftGrammar_rule, hinput]
  exact evaluates_liftExpr_with_blocked grammar suffix blocked evaluation

theorem evaluates_liftExpr_to_sentinel_iff
    (grammar : PegGrammar Terminal nonterminalCount)
    (total : grammar.IsLoffTotal)
    (expression : ParsingExpression Terminal nonterminalCount)
    (input : List (Option Terminal))
    (tail : List (Option Terminal)) :
    (liftGrammar grammar).Evaluates (liftExpr expression) input
        (.success (none :: tail)) ↔
      ∃ oldInput,
        input = liftWord oldInput ++ none :: tail ∧
          grammar.Evaluates expression oldInput (.success []) := by
  constructor
  · intro liftedEvaluation
    obtain ⟨oldInput, suffix, hinput, blocked⟩ :=
      exists_liftWord_append_blocked input
    obtain ⟨candidate, candidateEvaluation⟩ :=
      total expression oldInput
    have transported :
        (liftGrammar grammar).Evaluates (liftExpr expression) input
          (liftResult suffix candidate) := by
      rw [hinput]
      exact evaluates_liftExpr_with_blocked grammar suffix blocked
        candidateEvaluation
    have same :=
      PegSeparation.External.LoffForwardRepaired.PegGrammar.evaluates_deterministic
        transported liftedEvaluation
    cases candidate with
    | failure =>
        simp at same
    | success remaining =>
        rcases blocked with rfl | ⟨suffixTail, rfl⟩
        · cases remaining with
          | nil =>
              simp at same
          | cons symbol rest =>
              simp [liftWord] at same
        · cases remaining with
          | nil =>
              simp only [liftResult_success, liftWord_nil, List.nil_append,
                ParseResult.success.injEq] at same
              cases same
              exact ⟨oldInput, hinput, candidateEvaluation⟩
          | cons symbol rest =>
              simp [liftWord] at same
  · rintro ⟨oldInput, rfl, evaluation⟩
    simpa using
      evaluates_liftExpr_with_blocked grammar (none :: tail)
        (Or.inr ⟨tail, rfl⟩) evaluation

def LiftLanguage (language : Language Terminal) :
    Language (Option Terminal) := fun input =>
  ∃ word, word ∈ language ∧ input = liftWord word

theorem liftGrammar_recognizes_iff
    (grammar : PegGrammar Terminal nonterminalCount)
    (total : grammar.IsLoffTotal)
    (language : Language Terminal)
    (correct : ∀ input, grammar.Recognizes input ↔ input ∈ language)
    (input : List (Option Terminal)) :
    (liftGrammar grammar).Recognizes input ↔ input ∈ LiftLanguage language := by
  constructor
  · intro recognized
    obtain ⟨oldInput, suffix, hinput, blocked⟩ :=
      exists_liftWord_append_blocked input
    obtain ⟨candidate, candidateEvaluation⟩ :=
      total (.nonterminal grammar.start) oldInput
    have transported :
        (liftGrammar grammar).Evaluates
          (liftExpr (.nonterminal grammar.start)) input
          (liftResult suffix candidate) := by
      rw [hinput]
      exact evaluates_liftExpr_with_blocked grammar suffix blocked
        candidateEvaluation
    have same :=
      PegSeparation.External.LoffForwardRepaired.PegGrammar.evaluates_deterministic
        transported recognized
    cases candidate with
    | failure =>
        simp [PegGrammar.Recognizes] at same
    | success remaining =>
        have empty :
            liftWord remaining ++ suffix = [] := by
          simpa [PegGrammar.Recognizes] using same
        have remainingEmpty : remaining = [] := by
          have : liftWord remaining = [] :=
            (List.append_eq_nil_iff.mp empty).1
          exact (liftWord_eq_nil_iff remaining).mp this
        have suffixEmpty : suffix = [] :=
          (List.append_eq_nil_iff.mp empty).2
        subst remaining
        subst suffix
        refine ⟨oldInput, (correct oldInput).mp ?_, ?_⟩
        · exact candidateEvaluation
        · simpa using hinput
  · rintro ⟨word, member, rfl⟩
    have evaluation :
        grammar.Evaluates (.nonterminal grammar.start) word (.success []) :=
      (correct word).mpr member
    simpa [PegGrammar.Recognizes, liftExpr] using
      evaluates_liftExpr_with_blocked grammar []
        (Or.inl rfl) evaluation

theorem recognizedByTotalPEG_lift
    {language : Language Terminal}
    (recognized : RecognizedByTotalPEG language) :
    RecognizedByTotalPEG (LiftLanguage language) := by
  obtain ⟨count, grammar, total, correct⟩ := recognized
  exact ⟨count, liftGrammar grammar, liftGrammar_isLoffTotal grammar total,
    liftGrammar_recognizes_iff grammar total language correct⟩

end HomomorphismInternal

end PegSeparation.Closure
