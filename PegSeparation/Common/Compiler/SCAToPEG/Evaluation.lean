import PegSeparation.Common.Compiler.SCAToPEG.Construction


namespace PegSeparation.SCAToPEG

open PegSeparation

noncomputable section

section Generic

variable {Terminal : Type} [DecidableEq Terminal] {nonterminalCount : Nat}
variable {grammar : PegGrammar Terminal nonterminalCount}

theorem evaluates_choices_failure
    {expressions : List (ParsingExpression Terminal nonterminalCount)}
    {input : List Terminal}
    (allFail : ∀ expression ∈ expressions,
      grammar.Evaluates expression input .failure) :
    grammar.Evaluates (choices expressions) input .failure := by
  induction expressions with
  | nil => exact .failure input
  | cons expression expressions ih =>
      apply PegGrammar.Evaluates.choiceRight
      · exact allFail expression (by simp)
      · apply ih
        intro rest restMem
        exact allFail rest (by simp [restMem])

theorem evaluates_choices_success_of_append
    {before after : List (ParsingExpression Terminal nonterminalCount)}
    {selected : ParsingExpression Terminal nonterminalCount}
    {input remaining : List Terminal}
    (beforeFails : ∀ expression ∈ before,
      grammar.Evaluates expression input .failure)
    (selectedSucceeds : grammar.Evaluates selected input (.success remaining)) :
    grammar.Evaluates (choices (before ++ selected :: after)) input
      (.success remaining) := by
  induction before with
  | nil => exact .choiceLeft selectedSucceeds
  | cons expression before ih =>
      apply PegGrammar.Evaluates.choiceRight
      · exact beforeFails expression (by simp)
      · apply ih
        intro rest restMem
        exact beforeFails rest (by simp [restMem])

theorem evaluates_sequences_success_same_input
    {expressions : List (ParsingExpression Terminal nonterminalCount)}
    {input : List Terminal}
    (allSucceed : ∀ expression ∈ expressions,
      grammar.Evaluates expression input (.success input)) :
    grammar.Evaluates (sequences expressions) input (.success input) := by
  induction expressions with
  | nil => exact .empty input
  | cons expression expressions ih =>
      apply PegGrammar.Evaluates.sequenceSuccess
      · exact allSucceed expression (by simp)
      · apply ih
        intro rest restMem
        exact allSucceed rest (by simp [restMem])

theorem evaluates_sequences_failure_of_append
    {before after : List (ParsingExpression Terminal nonterminalCount)}
    {selected : ParsingExpression Terminal nonterminalCount}
    {input : List Terminal}
    (beforeSucceeds : ∀ expression ∈ before,
      grammar.Evaluates expression input (.success input))
    (selectedFails : grammar.Evaluates selected input .failure) :
    grammar.Evaluates (sequences (before ++ selected :: after)) input .failure := by
  induction before with
  | nil => exact .sequenceFailure selectedFails
  | cons expression before ih =>
      apply PegGrammar.Evaluates.sequenceSuccess
      · exact beforeSucceeds expression (by simp)
      · apply ih
        intro rest restMem
        exact beforeSucceeds rest (by simp [restMem])


theorem evaluates_terminal_match (symbol : Terminal) (rest : List Terminal) :
    grammar.Evaluates (.terminal symbol) (symbol :: rest) (.success rest) := by
  simpa [PegGrammar.terminalResult] using
    (PegGrammar.Evaluates.terminal (grammar := grammar) symbol (symbol :: rest))

theorem evaluates_terminal_mismatch {wanted actual : Terminal}
    (different : actual ≠ wanted) (rest : List Terminal) :
    grammar.Evaluates (.terminal wanted) (actual :: rest) .failure := by
  simpa [PegGrammar.terminalResult, different] using
    (PegGrammar.Evaluates.terminal (grammar := grammar) wanted (actual :: rest))

theorem evaluates_terminal_empty (wanted : Terminal) :
    grammar.Evaluates (.terminal wanted) [] .failure := by
  simpa [PegGrammar.terminalResult] using
    (PegGrammar.Evaluates.terminal (grammar := grammar) wanted [])

theorem evaluates_terminal_choices_success_of_mem
    {symbols : List Terminal} {symbol : Terminal} (rest : List Terminal)
    (member : symbol ∈ symbols) :
    grammar.Evaluates
      (choices (symbols.map ParsingExpression.terminal))
      (symbol :: rest) (.success rest) := by
  induction symbols with
  | nil => simp at member
  | cons head tail ih =>
      by_cases equal : head = symbol
      · subst head
        exact .choiceLeft (evaluates_terminal_match symbol rest)
      · apply PegGrammar.Evaluates.choiceRight
        · exact evaluates_terminal_mismatch (Ne.symm equal) rest
        · apply ih
          simpa [Ne.symm equal] using member

theorem evaluates_terminal_choices_failure_of_not_mem
    {symbols : List Terminal} {symbol : Terminal} (rest : List Terminal)
    (notMember : symbol ∉ symbols) :
    grammar.Evaluates
      (choices (symbols.map ParsingExpression.terminal))
      (symbol :: rest) .failure := by
  induction symbols with
  | nil => exact .failure (symbol :: rest)
  | cons head tail ih =>
      have different : symbol ≠ head := by
        intro equal
        apply notMember
        simp [equal]
      apply PegGrammar.Evaluates.choiceRight
      · exact evaluates_terminal_mismatch different rest
      · apply ih
        exact fun member => notMember (by simp [member])

theorem evaluates_terminal_choices_empty (symbols : List Terminal) :
    grammar.Evaluates
      (choices (symbols.map ParsingExpression.terminal)) [] .failure := by
  induction symbols with
  | nil => exact .failure []
  | cons head tail ih =>
      exact .choiceRight (evaluates_terminal_empty head) ih


section Keyed

variable {Key : Type} [DecidableEq Key]

theorem evaluates_keyed_choices_of_unique_success
    {keys : List Key} {wanted : Key}
    {test continuation : Key → ParsingExpression Terminal nonterminalCount}
    {input middle remaining : List Terminal}
    (member : wanted ∈ keys)
    (wantedTest : grammar.Evaluates (test wanted) input (.success middle))
    (wantedContinuation :
      grammar.Evaluates (continuation wanted) middle (.success remaining))
    (otherTestsFail : ∀ key ∈ keys, key ≠ wanted →
      grammar.Evaluates (test key) input .failure) :
    grammar.Evaluates
      (choices (keys.map fun key =>
        .sequence (test key) (continuation key)))
      input (.success remaining) := by
  induction keys with
  | nil => simp at member
  | cons key keys ih =>
      by_cases equal : key = wanted
      · subst key
        exact .choiceLeft (.sequenceSuccess wantedTest wantedContinuation)
      · apply PegGrammar.Evaluates.choiceRight
        · exact .sequenceFailure (otherTestsFail key (by simp) equal)
        · apply ih
          · simpa [Ne.symm equal] using member
          · intro other otherMem otherNe
            exact otherTestsFail other (by simp [otherMem]) otherNe

omit [DecidableEq Key] in
theorem evaluates_keyed_choices_failure
    {keys : List Key}
    {test continuation : Key → ParsingExpression Terminal nonterminalCount}
    {input : List Terminal}
    (testsFail : ∀ key ∈ keys,
      grammar.Evaluates (test key) input .failure) :
    grammar.Evaluates
      (choices (keys.map fun key =>
        .sequence (test key) (continuation key)))
      input .failure := by
  apply evaluates_choices_failure
  intro expression expressionMem
  simp only [List.mem_map] at expressionMem
  obtain ⟨key, keyMem, rfl⟩ := expressionMem
  exact .sequenceFailure (testsFail key keyMem)

theorem evaluates_keyed_choices_of_unique
    {keys : List Key} {wanted : Key}
    {test continuation : Key → ParsingExpression Terminal nonterminalCount}
    {input middle : List Terminal} {result : ParseResult Terminal}
    (member : wanted ∈ keys)
    (wantedTest : grammar.Evaluates (test wanted) input (.success middle))
    (wantedContinuation : grammar.Evaluates (continuation wanted) middle result)
    (otherTestsFail : ∀ key ∈ keys, key ≠ wanted →
      grammar.Evaluates (test key) input .failure) :
    grammar.Evaluates
      (choices (keys.map fun key =>
        .sequence (test key) (continuation key))) input result := by
  cases result with
  | success remaining =>
      exact evaluates_keyed_choices_of_unique_success member wantedTest
        wantedContinuation otherTestsFail
  | failure =>
      apply evaluates_choices_failure
      intro expression expressionMem
      simp only [List.mem_map] at expressionMem
      obtain ⟨key, keyMem, rfl⟩ := expressionMem
      by_cases equal : key = wanted
      · subst key
        exact .sequenceSuccess wantedTest wantedContinuation
      · exact .sequenceFailure (otherTestsFail key keyMem equal)

end Keyed

end Generic


section Construction

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
variable {stateCount workLabelCount degree radius : Nat}

local notation "Expr" =>
  ParsingExpression Terminal (NameCount stateCount workLabelCount degree radius)

variable {grammar :
  PegGrammar Terminal (NameCount stateCount workLabelCount degree radius)}

theorem evaluates_anyTerminal_cons (symbol : Terminal) (rest : List Terminal) :
    grammar.Evaluates
      (anyTerminal (Terminal := Terminal) (stateCount := stateCount)
        (workLabelCount := workLabelCount) (degree := degree) (radius := radius))
      (symbol :: rest) (.success rest) := by
  unfold anyTerminal
  apply evaluates_terminal_choices_success_of_mem
  simp

theorem evaluates_anyTerminal_empty :
    grammar.Evaluates
      (anyTerminal (Terminal := Terminal) (stateCount := stateCount)
        (workLabelCount := workLabelCount) (degree := degree) (radius := radius))
      [] .failure := by
  unfold anyTerminal
  exact evaluates_terminal_choices_empty _

theorem evaluates_endOfInput_empty :
    grammar.Evaluates
      (endOfInput (Terminal := Terminal) (stateCount := stateCount)
        (workLabelCount := workLabelCount) (degree := degree) (radius := radius))
      [] (.success []) := by
  unfold endOfInput
  exact .notSuccess evaluates_anyTerminal_empty

theorem evaluates_endOfInput_cons (symbol : Terminal) (rest : List Terminal) :
    grammar.Evaluates
      (endOfInput (Terminal := Terminal) (stateCount := stateCount)
        (workLabelCount := workLabelCount) (degree := degree) (radius := radius))
      (symbol :: rest) .failure := by
  unfold endOfInput
  exact .notFailure (evaluates_anyTerminal_cons symbol rest)

theorem evaluates_dispatch_of_unique
    {continuation :
      TransitionKey Terminal stateCount workLabelCount degree radius → Expr}
    {wanted : TransitionKey Terminal stateCount workLabelCount degree radius}
    {input middle : List Terminal} {result : ParseResult Terminal}
    (wantedTest : grammar.Evaluates
      (transitionTest wanted) input (.success middle))
    (wantedContinuation : grammar.Evaluates (continuation wanted) middle result)
    (otherTestsFail : ∀ key, key ≠ wanted →
      grammar.Evaluates (transitionTest key) input .failure) :
    grammar.Evaluates
      (dispatch continuation) input result := by
  unfold dispatch
  apply evaluates_keyed_choices_of_unique
  · simp
  · exact wantedTest
  · exact wantedContinuation
  · intro key _ keyNe
    exact otherTestsFail key keyNe

theorem evaluates_dispatch_failure
    {continuation :
      TransitionKey Terminal stateCount workLabelCount degree radius → Expr}
    {input : List Terminal}
    (testsFail : ∀ key,
      grammar.Evaluates (transitionTest key) input .failure) :
    grammar.Evaluates (dispatch continuation) input .failure := by
  unfold dispatch
  apply evaluates_keyed_choices_failure
  intro key _
  exact testsFail key

end Construction

end

end PegSeparation.SCAToPEG
