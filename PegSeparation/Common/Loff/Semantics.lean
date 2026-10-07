import PegSeparation.Common.Loff.ScaffoldView
import PegSeparation.Common.Model.PEG


namespace PegSeparation.External.LoffForwardRepaired

open PegSeparation

namespace PegGrammar

variable {Terminal : Type} [DecidableEq Terminal]
  {nonterminalCount : Nat}
  {grammar : PegSeparation.PegGrammar Terminal nonterminalCount}

theorem evaluates_deterministic
    {expression : ParsingExpression Terminal nonterminalCount}
    {input : List Terminal} {first second : ParseResult Terminal}
    (hfirst : grammar.Evaluates expression input first)
    (hsecond : grammar.Evaluates expression input second) : first = second := by
  induction hfirst generalizing second with
  | empty input =>
      cases hsecond
      rfl
  | failure input =>
      cases hsecond
      rfl
  | terminal symbol input =>
      cases hsecond
      rfl
  | nonterminal body ih =>
      cases hsecond with
      | nonterminal body' => exact ih body'
  | sequenceFailure leftFails ih =>
      cases hsecond with
      | sequenceFailure leftFails' => rfl
      | sequenceSuccess leftSucceeds rightResult =>
          have : ParseResult.failure = ParseResult.success _ := ih leftSucceeds
          contradiction
  | sequenceSuccess leftSucceeds rightResult ihLeft ihRight =>
      cases hsecond with
      | sequenceFailure leftFails =>
          have : ParseResult.success _ = ParseResult.failure := ihLeft leftFails
          contradiction
      | sequenceSuccess leftSucceeds' rightResult' =>
          have hmiddle : _ = _ := ihLeft leftSucceeds'
          cases hmiddle
          exact ihRight rightResult'
  | choiceLeft leftSucceeds ih =>
      cases hsecond with
      | choiceLeft leftSucceeds' =>
          have hremaining := ih leftSucceeds'
          cases hremaining
          rfl
      | choiceRight leftFails rightResult =>
          have : ParseResult.success _ = ParseResult.failure := ih leftFails
          contradiction
  | choiceRight leftFails rightResult ihLeft ihRight =>
      cases hsecond with
      | choiceLeft leftSucceeds =>
          have : ParseResult.failure = ParseResult.success _ := ihLeft leftSucceeds
          contradiction
      | choiceRight leftFails' rightResult' => exact ihRight rightResult'
  | notSuccess bodyFails ih =>
      cases hsecond with
      | notSuccess bodyFails' => rfl
      | notFailure bodySucceeds =>
          have : ParseResult.failure = ParseResult.success _ := ih bodySucceeds
          contradiction
  | notFailure bodySucceeds ih =>
      cases hsecond with
      | notSuccess bodyFails =>
          have : ParseResult.success _ = ParseResult.failure := ih bodyFails
          contradiction
      | notFailure bodySucceeds' => rfl
  | andSuccess bodySucceeds ih =>
      cases hsecond with
      | andSuccess bodySucceeds' => rfl
      | andFailure bodyFails =>
          have : ParseResult.success _ = ParseResult.failure := ih bodyFails
          contradiction
  | andFailure bodyFails ih =>
      cases hsecond with
      | andSuccess bodySucceeds =>
          have : ParseResult.failure = ParseResult.success _ := ih bodySucceeds
          contradiction
      | andFailure bodyFails' => rfl

private theorem success_isSuffix_aux
    {expression : ParsingExpression Terminal nonterminalCount}
    {input : List Terminal} {parseResult : ParseResult Terminal}
    (evaluation : grammar.Evaluates expression input parseResult) :
    ∀ {remaining : List Terminal}, parseResult = .success remaining → remaining <:+ input := by
  induction evaluation with
  | empty =>
      intro remaining heq
      cases heq
      simp
  | failure => simp
  | terminal symbol input =>
      intro remaining heq
      cases input with
      | nil => simp [PegGrammar.terminalResult] at heq
      | cons actual rest =>
          simp only [PegGrammar.terminalResult] at heq
          split at heq
          · cases heq
            exact ⟨[actual], by simp⟩
          · contradiction
  | nonterminal body ih => exact ih
  | sequenceFailure => simp
  | sequenceSuccess leftSucceeds rightResult ihLeft ihRight =>
      intro remaining heq
      exact (ihRight heq).trans (ihLeft rfl)
  | choiceLeft leftSucceeds ih =>
      intro remaining heq
      exact ih heq
  | choiceRight leftFails rightResult ihLeft ihRight => exact ihRight
  | notSuccess bodyFails ih =>
      intro remaining heq
      cases heq
      simp
  | notFailure => simp
  | andSuccess bodySucceeds ih =>
      intro remaining heq
      cases heq
      simp
  | andFailure => simp

theorem success_isSuffix
    {expression : ParsingExpression Terminal nonterminalCount}
    {input remaining : List Terminal}
    (evaluation : grammar.Evaluates expression input (.success remaining)) :
    remaining <:+ input :=
  success_isSuffix_aux evaluation rfl

theorem success_on_nil
    {expression : ParsingExpression Terminal nonterminalCount}
    {remaining : List Terminal}
    (evaluation : grammar.Evaluates expression [] (.success remaining)) :
    remaining = [] := by
  have hsuffix := success_isSuffix evaluation
  simpa using hsuffix

end PegGrammar


section Expressions

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
  {nonterminalCount : Nat}

private noncomputable instance expressionDecidableEq :
    DecidableEq (ParsingExpression Terminal nonterminalCount) := Classical.decEq _

noncomputable def subexpressions :
    ParsingExpression Terminal nonterminalCount →
      Finset (ParsingExpression Terminal nonterminalCount)
  | expression@(.empty) => {expression}
  | expression@(.failure) => {expression}
  | expression@(.terminal _) => {expression}
  | expression@(.nonterminal _) => {expression}
  | expression@(.sequence left right) =>
      insert expression (subexpressions left ∪ subexpressions right)
  | expression@(.orderedChoice left right) =>
      insert expression (subexpressions left ∪ subexpressions right)
  | expression@(.notPredicate body) => insert expression (subexpressions body)
  | expression@(.andPredicate body) => insert expression (subexpressions body)

@[simp] theorem mem_subexpressions_self
    (expression : ParsingExpression Terminal nonterminalCount) :
    expression ∈ subexpressions expression := by
  cases expression <;> simp [subexpressions]

noncomputable def relevantExpressions
    (grammar : PegGrammar Terminal nonterminalCount) :
    Finset (ParsingExpression Terminal nonterminalCount) :=
  Finset.univ.biUnion fun name =>
    insert (.nonterminal name) (subexpressions (grammar.rule name))

@[simp] theorem nonterminal_mem_relevantExpressions
    (grammar : PegGrammar Terminal nonterminalCount) (name : Fin nonterminalCount) :
    .nonterminal name ∈ relevantExpressions grammar := by
  classical
  simp [relevantExpressions]

@[simp] theorem rule_mem_relevantExpressions
    (grammar : PegGrammar Terminal nonterminalCount) (name : Fin nonterminalCount) :
    grammar.rule name ∈ relevantExpressions grammar := by
  classical
  rw [relevantExpressions, Finset.mem_biUnion]
  exact ⟨name, Finset.mem_univ _, by simp⟩

theorem mem_subexpressions_trans
    {small middle large : ParsingExpression Terminal nonterminalCount}
    (hsmall : small ∈ subexpressions middle)
    (hmiddle : middle ∈ subexpressions large) :
    small ∈ subexpressions large := by
  induction large generalizing middle small with
  | empty =>
      simp [subexpressions] at hmiddle
      subst middle
      exact hsmall
  | failure =>
      simp [subexpressions] at hmiddle
      subst middle
      exact hsmall
  | terminal symbol =>
      simp [subexpressions] at hmiddle
      subst middle
      exact hsmall
  | nonterminal name =>
      simp [subexpressions] at hmiddle
      subst middle
      exact hsmall
  | sequence left right ihLeft ihRight =>
      simp only [subexpressions, Finset.mem_insert, Finset.mem_union] at hmiddle ⊢
      rcases hmiddle with rfl | hmiddle | hmiddle
      · simpa [subexpressions] using hsmall
      · exact Or.inr (Or.inl (ihLeft hsmall hmiddle))
      · exact Or.inr (Or.inr (ihRight hsmall hmiddle))
  | orderedChoice left right ihLeft ihRight =>
      simp only [subexpressions, Finset.mem_insert, Finset.mem_union] at hmiddle ⊢
      rcases hmiddle with rfl | hmiddle | hmiddle
      · simpa [subexpressions] using hsmall
      · exact Or.inr (Or.inl (ihLeft hsmall hmiddle))
      · exact Or.inr (Or.inr (ihRight hsmall hmiddle))
  | notPredicate body ih =>
      simp only [subexpressions, Finset.mem_insert] at hmiddle ⊢
      rcases hmiddle with rfl | hmiddle
      · simpa [subexpressions] using hsmall
      · exact Or.inr (ih hsmall hmiddle)
  | andPredicate body ih =>
      simp only [subexpressions, Finset.mem_insert] at hmiddle ⊢
      rcases hmiddle with rfl | hmiddle
      · simpa [subexpressions] using hsmall
      · exact Or.inr (ih hsmall hmiddle)

theorem subexpression_mem_relevantExpressions
    (grammar : PegGrammar Terminal nonterminalCount)
    {parent child : ParsingExpression Terminal nonterminalCount}
    (hparent : parent ∈ relevantExpressions grammar)
    (hchild : child ∈ subexpressions parent) :
    child ∈ relevantExpressions grammar := by
  classical
  rw [relevantExpressions, Finset.mem_biUnion] at hparent ⊢
  rcases hparent with ⟨name, _, hparent⟩
  simp only [Finset.mem_insert] at hparent
  rcases hparent with hparent | hparent
  · subst parent
    simp [subexpressions] at hchild
    subst child
    exact ⟨name, Finset.mem_univ _, by simp⟩
  · refine ⟨name, Finset.mem_univ _, ?_⟩
    simp only [Finset.mem_insert]
    exact Or.inr (mem_subexpressions_trans hchild hparent)

abbrev Coordinate (grammar : PegGrammar Terminal nonterminalCount) :=
  { expression // expression ∈ relevantExpressions grammar }

end Expressions


inductive Status where
  | failure
  | zero
  | past
  | base
  deriving DecidableEq, Fintype, Repr

namespace Semantic

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
  {nonterminalCount : Nat}
  (grammar : PegGrammar Terminal nonterminalCount)
  (total : grammar.IsLoffTotal)

noncomputable def result
    (expression : ParsingExpression Terminal nonterminalCount)
    (input : List Terminal) : ParseResult Terminal :=
  Classical.choose (total expression input)

theorem result_spec
    (expression : ParsingExpression Terminal nonterminalCount)
    (input : List Terminal) :
    grammar.Evaluates expression input (result grammar total expression input) :=
  Classical.choose_spec (total expression input)

theorem result_eq_of_evaluates
    {expression : ParsingExpression Terminal nonterminalCount}
    {input : List Terminal} {parseResult : ParseResult Terminal}
    (evaluation : grammar.Evaluates expression input parseResult) :
    result grammar total expression input = parseResult :=
  PegGrammar.evaluates_deterministic (result_spec grammar total expression input) evaluation

noncomputable def status
    (expression : ParsingExpression Terminal nonterminalCount)
    (input : List Terminal) : Status :=
  match result grammar total expression input with
  | .failure => .failure
  | .success remaining =>
      if remaining = input then .zero
      else if remaining = [] then .base
      else .past

theorem result_success_isSuffix
    {expression : ParsingExpression Terminal nonterminalCount}
    {input remaining : List Terminal}
    (hresult : result grammar total expression input = .success remaining) :
    remaining <:+ input := by
  apply PegGrammar.success_isSuffix
  simpa [hresult] using result_spec grammar total expression input

theorem status_on_nil
    (expression : ParsingExpression Terminal nonterminalCount) :
    status grammar total expression [] = .failure ∨
      status grammar total expression [] = .zero := by
  rw [status]
  split
  · exact Or.inl rfl
  · rename_i remaining heq
    have hnil : remaining = [] := by
      apply PegGrammar.success_on_nil
      simpa [heq] using result_spec grammar total expression []
    subst remaining
    exact Or.inr (by simp)

@[simp] theorem result_empty (input : List Terminal) :
    result grammar total .empty input = .success input :=
  result_eq_of_evaluates grammar total (.empty input)

@[simp] theorem result_failure (input : List Terminal) :
    result grammar total .failure input = .failure :=
  result_eq_of_evaluates grammar total (.failure input)

@[simp] theorem result_terminal (symbol : Terminal) (input : List Terminal) :
    result grammar total (.terminal symbol) input =
      PegGrammar.terminalResult symbol input :=
  result_eq_of_evaluates grammar total (.terminal symbol input)

@[simp] theorem result_nonterminal (name : Fin nonterminalCount) (input : List Terminal) :
    result grammar total (.nonterminal name) input =
      result grammar total (grammar.rule name) input := by
  apply result_eq_of_evaluates grammar total
  exact .nonterminal (result_spec grammar total (grammar.rule name) input)

theorem result_sequence_of_failure
    {left right : ParsingExpression Terminal nonterminalCount}
    {input : List Terminal}
    (hleft : result grammar total left input = .failure) :
    result grammar total (.sequence left right) input = .failure := by
  apply result_eq_of_evaluates grammar total
  exact .sequenceFailure (by simpa [hleft] using result_spec grammar total left input)

theorem result_sequence_of_success
    {left right : ParsingExpression Terminal nonterminalCount}
    {input middle : List Terminal}
    (hleft : result grammar total left input = .success middle) :
    result grammar total (.sequence left right) input =
      result grammar total right middle := by
  apply result_eq_of_evaluates grammar total
  exact .sequenceSuccess
    (by simpa [hleft] using result_spec grammar total left input)
    (result_spec grammar total right middle)

theorem result_choice_of_success
    {left right : ParsingExpression Terminal nonterminalCount}
    {input remaining : List Terminal}
    (hleft : result grammar total left input = .success remaining) :
    result grammar total (.orderedChoice left right) input = .success remaining := by
  apply result_eq_of_evaluates grammar total
  exact .choiceLeft (by simpa [hleft] using result_spec grammar total left input)

theorem result_choice_of_failure
    {left right : ParsingExpression Terminal nonterminalCount}
    {input : List Terminal}
    (hleft : result grammar total left input = .failure) :
    result grammar total (.orderedChoice left right) input =
      result grammar total right input := by
  apply result_eq_of_evaluates grammar total
  exact .choiceRight
    (by simpa [hleft] using result_spec grammar total left input)
    (result_spec grammar total right input)

theorem result_not_of_failure
    {body : ParsingExpression Terminal nonterminalCount} {input : List Terminal}
    (hbody : result grammar total body input = .failure) :
    result grammar total (.notPredicate body) input = .success input := by
  apply result_eq_of_evaluates grammar total
  exact .notSuccess (by simpa [hbody] using result_spec grammar total body input)

theorem result_not_of_success
    {body : ParsingExpression Terminal nonterminalCount}
    {input remaining : List Terminal}
    (hbody : result grammar total body input = .success remaining) :
    result grammar total (.notPredicate body) input = .failure := by
  apply result_eq_of_evaluates grammar total
  exact .notFailure (by simpa [hbody] using result_spec grammar total body input)

theorem result_and_of_failure
    {body : ParsingExpression Terminal nonterminalCount} {input : List Terminal}
    (hbody : result grammar total body input = .failure) :
    result grammar total (.andPredicate body) input = .failure := by
  apply result_eq_of_evaluates grammar total
  exact .andFailure (by simpa [hbody] using result_spec grammar total body input)

theorem result_and_of_success
    {body : ParsingExpression Terminal nonterminalCount}
    {input remaining : List Terminal}
    (hbody : result grammar total body input = .success remaining) :
    result grammar total (.andPredicate body) input = .success input := by
  apply result_eq_of_evaluates grammar total
  exact .andSuccess (by simpa [hbody] using result_spec grammar total body input)

theorem status_eq_failure_iff
    (expression : ParsingExpression Terminal nonterminalCount) (input : List Terminal) :
    status grammar total expression input = .failure ↔
      result grammar total expression input = .failure := by
  constructor
  · intro hstatus
    cases hresult : result grammar total expression input with
    | failure => rfl
    | success remaining =>
        rw [status, hresult] at hstatus
        by_cases hsame : remaining = input
        · simp [hsame] at hstatus
        · by_cases hnil : remaining = []
          · by_cases hinput : input = [] <;>
              simp [hsame, hnil, hinput] at hstatus
          · simp [hsame, hnil] at hstatus
  · intro hresult
    simp [status, hresult]

theorem status_eq_zero_iff
    (expression : ParsingExpression Terminal nonterminalCount) (input : List Terminal) :
    status grammar total expression input = .zero ↔
      result grammar total expression input = .success input := by
  constructor
  · intro hstatus
    cases hresult : result grammar total expression input with
    | failure => simp [status, hresult] at hstatus
    | success remaining =>
        have hsame : remaining = input := by
          by_cases hsame : remaining = input
          · exact hsame
          · by_cases hnil : remaining = []
            · simp [status, hresult, hsame, hnil] at hstatus
              exact hnil.trans hstatus.symm
            · simp [status, hresult, hsame, hnil] at hstatus
        simpa [hsame] using hresult
  · intro hresult
    simp [status, hresult]

theorem status_eq_base_iff
    (expression : ParsingExpression Terminal nonterminalCount)
    {input : List Terminal} (hne : input ≠ []) :
    status grammar total expression input = .base ↔
      result grammar total expression input = .success [] := by
  constructor
  · intro hstatus
    cases hresult : result grammar total expression input with
    | failure => simp [status, hresult] at hstatus
    | success remaining =>
        have hnil : remaining = [] := by
          by_cases hsame : remaining = input
          · simp [status, hresult, hsame] at hstatus
          · simpa [status, hresult, hsame] using hstatus
        simpa [hnil]
  · intro hresult
    simp [status, hresult, hne]

theorem status_eq_past_iff
    (expression : ParsingExpression Terminal nonterminalCount) (input : List Terminal) :
    status grammar total expression input = .past ↔
      ∃ remaining, result grammar total expression input = .success remaining ∧
        remaining ≠ input ∧ remaining ≠ [] := by
  constructor
  · intro hstatus
    cases hresult : result grammar total expression input with
    | failure => simp [status, hresult] at hstatus
    | success remaining =>
        have hsame : remaining ≠ input := by
          intro hsame
          simp [status, hresult, hsame] at hstatus
        have hnil : remaining ≠ [] := by
          intro hnil
          by_cases hinput : input = []
          · exact hsame (hnil.trans hinput.symm)
          · simp [status, hresult, hnil, hinput] at hstatus
        exact ⟨remaining, rfl, hsame, hnil⟩
  · rintro ⟨remaining, hresult, hsame, hnil⟩
    simp [status, hresult, hsame, hnil]

end Semantic

end PegSeparation.External.LoffForwardRepaired
