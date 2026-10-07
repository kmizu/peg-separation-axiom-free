import PegSeparation.CFLNotPEG.Witness.DirectPEG
import PegSeparation.External.PartialTotalization.TotalityHelpers


namespace PegSeparation.Witness.DirectPEG

open PegSeparation
open PegSeparation.PegGrammar.PartialTotalityHelpers

private abbrev CallTotal (name : Fin 10) (input : Word) : Prop :=
  ∃ result, grammar.Evaluates (.nonterminal name) input result

private theorem terminal_total (symbol : Terminal) (input : Word) :
    ∃ result, grammar.Evaluates (.terminal symbol) input result :=
  ⟨PegGrammar.terminalResult symbol input, .terminal symbol input⟩

private theorem terminalResult_success_length_lt
    {wanted : Terminal} {input remaining : Word}
    (resultEquation :
      PegGrammar.terminalResult wanted input = .success remaining) :
    remaining.length < input.length := by
  cases input with
  | nil =>
      simp [PegGrammar.terminalResult] at resultEquation
  | cons actual rest =>
      simp only [PegGrammar.terminalResult] at resultEquation
      split at resultEquation
      · cases resultEquation
        simp
      · contradiction

private theorem terminal_sequence_success_length_lt
    {wanted : Terminal} {body : Expr} {input remaining : Word}
    (evaluation :
      grammar.Evaluates
        (.sequence (.terminal wanted) body) input (.success remaining)) :
    remaining.length < input.length := by
  cases evaluation with
  | sequenceSuccess leftEvaluation rightEvaluation =>
      have resultEquation :
          PegGrammar.terminalResult wanted input = .success _ :=
        (PegSeparation.External.LoffForwardRepaired.PegGrammar.evaluates_deterministic
            (PegGrammar.Evaluates.terminal
              (grammar := grammar) wanted input)
            leftEvaluation)
      have middleLt :=
        terminalResult_success_length_lt
          (wanted := wanted)
          (input := input)
          (remaining := _)
          resultEquation
      have remainingLe :
          remaining.length ≤ _ :=
        (PegSeparation.External.LoffForwardRepaired.PegGrammar.success_isSuffix
          rightEvaluation).length_le
      omega

private theorem terminal_success_length_lt
    {wanted : Terminal} {input remaining : Word}
    (evaluation :
      grammar.Evaluates (.terminal wanted) input (.success remaining)) :
    remaining.length < input.length := by
  apply terminalResult_success_length_lt
  exact
    PegSeparation.External.LoffForwardRepaired.PegGrammar.evaluates_deterministic
      (PegGrammar.Evaluates.terminal
        (grammar := grammar) wanted input)
      evaluation

private theorem sequence_total_of_success_shorter
    {left right : Expr} {input : Word}
    (leftTotal : ∃ result, grammar.Evaluates left input result)
    (leftShort :
      ∀ middle,
        grammar.Evaluates left input (.success middle) →
        middle.length < input.length)
    (rightTotal :
      ∀ middle, middle.length < input.length →
        ∃ result, grammar.Evaluates right middle result) :
    ∃ result, grammar.Evaluates (.sequence left right) input result := by
  obtain ⟨leftResult, leftEvaluation⟩ := leftTotal
  cases leftResult with
  | failure =>
      exact ⟨.failure, .sequenceFailure leftEvaluation⟩
  | success middle =>
      obtain ⟨rightResult, rightEvaluation⟩ :=
        rightTotal middle (leftShort middle leftEvaluation)
      exact ⟨rightResult,
        .sequenceSuccess leftEvaluation rightEvaluation⟩

private theorem expression_total_below
    (bound : Nat)
    (calls :
      ∀ name input, input.length < bound → CallTotal name input) :
    ∀ expression input, input.length < bound →
      ∃ result, grammar.Evaluates expression input result := by
  intro expression
  induction expression with
  | empty =>
      intro input _
      exact ⟨.success input, .empty input⟩
  | failure =>
      intro input _
      exact ⟨.failure, .failure input⟩
  | terminal symbol =>
      intro input _
      exact terminal_total symbol input
  | nonterminal name =>
      intro input short
      exact calls name input short
  | sequence left right leftTotal rightTotal =>
      intro input short
      obtain ⟨leftResult, leftEvaluation⟩ :=
        leftTotal input short
      cases leftResult with
      | failure =>
          exact ⟨.failure, .sequenceFailure leftEvaluation⟩
      | success middle =>
          have middleShort : middle.length < bound :=
            lt_of_le_of_lt
              (PegSeparation.External.LoffForwardRepaired.PegGrammar.success_isSuffix
                leftEvaluation).length_le
              short
          obtain ⟨rightResult, rightEvaluation⟩ :=
            rightTotal middle middleShort
          exact ⟨rightResult,
            .sequenceSuccess leftEvaluation rightEvaluation⟩
  | orderedChoice left right leftTotal rightTotal =>
      intro input short
      exact orderedChoice_total
        (leftTotal input short) (rightTotal input short)
  | notPredicate body bodyTotal =>
      intro input short
      exact notPredicate_total (bodyTotal input short)
  | andPredicate body bodyTotal =>
      intro input short
      exact andPredicate_total (bodyTotal input short)

private theorem bit_success_length_lt
    {input remaining : Word}
    (evaluation :
      grammar.Evaluates
        (.nonterminal bitName) input (.success remaining)) :
    remaining.length < input.length := by
  cases evaluation with
  | nonterminal bodyEvaluation =>
      have ruleEvaluation :
          grammar.Evaluates bitRule input (.success remaining) := by
        simpa using bodyEvaluation
      cases ruleEvaluation with
      | choiceLeft zeroEvaluation =>
          exact terminal_success_length_lt zeroEvaluation
      | choiceRight _ oneEvaluation =>
          exact terminal_success_length_lt oneEvaluation

private theorem entry_success_length_lt
    {input remaining : Word}
    (evaluation :
      grammar.Evaluates
        (.nonterminal entryName) input (.success remaining)) :
    remaining.length < input.length := by
  cases evaluation with
  | nonterminal bodyEvaluation =>
      have ruleEvaluation :
          grammar.Evaluates entryRule input (.success remaining) := by
        simpa using bodyEvaluation
      change
        grammar.Evaluates
          (.sequence (.terminal .langle) _) input (.success remaining)
        at ruleEvaluation
      exact terminal_sequence_success_length_lt ruleEvaluation

theorem nonterminal_call_total (name : Fin 10) (input : Word) :
    ∃ result,
      grammar.Evaluates (.nonterminal name) input result := by
  have bounded :
      ∀ n (input : Word), input.length = n →
        ∀ name, CallTotal name input := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n inductionHypothesis =>
      intro input inputLength
      have smallerCall
          (name : Fin 10) (smaller : Word)
          (short : smaller.length < input.length) :
          CallTotal name smaller :=
        inductionHypothesis smaller.length (by omega)
          smaller rfl name
      have smallerExpression
          (expression : Expr) (smaller : Word)
          (short : smaller.length < input.length) :
          ∃ result, grammar.Evaluates expression smaller result :=
        expression_total_below input.length
          (fun smallerName smallerInput smallerShort =>
            smallerCall smallerName smallerInput smallerShort)
          expression smaller short
      have bitBodyTotal :
          ∃ result, grammar.Evaluates bitRule input result := by
        exact orderedChoice_total
          (terminal_total .bit0 input)
          (terminal_total .bit1 input)
      have bitTotal : CallTotal bitName input :=
        bitBodyTotal.imp fun _ evaluation =>
          .nonterminal (by simpa using evaluation)
      have bitsRecursiveTotal :
          ∃ result,
            grammar.Evaluates
              (.sequence
                (.nonterminal bitName)
                (.nonterminal bitsName))
              input result :=
        sequence_total_of_success_shorter
          bitTotal
          (fun _ evaluation =>
            bit_success_length_lt evaluation)
          (fun smaller short =>
            smallerExpression
              (.nonterminal bitsName) smaller short)
      have bitsBodyTotal :
          ∃ result, grammar.Evaluates bitsRule input result := by
        change
          ∃ result,
            grammar.Evaluates
              (.orderedChoice
                (.sequence
                  (.nonterminal bitName)
                  (.nonterminal bitsName))
                (.nonterminal bitName))
              input result
        exact orderedChoice_total bitsRecursiveTotal bitTotal
      have bitsTotal : CallTotal bitsName input :=
        bitsBodyTotal.imp fun _ evaluation =>
          .nonterminal (by simpa using evaluation)
      have entryBodyTotal :
          ∃ result, grammar.Evaluates entryRule input result := by
        change
          ∃ result,
            grammar.Evaluates
              (.sequence
                (.terminal .langle)
                (.sequence
                  (.nonterminal bitsName)
                  (.sequence
                    (.terminal .colon)
                    (.sequence
                      (.nonterminal bitsName)
                      (.terminal .rangle)))))
              input result
        exact sequence_total_of_success_shorter
          (terminal_total .langle input)
          (fun _ evaluation =>
            terminal_success_length_lt evaluation)
          (fun smaller short =>
            smallerExpression _ smaller short)
      have entryTotal : CallTotal entryName input :=
        entryBodyTotal.imp fun _ evaluation =>
          .nonterminal (by simpa using evaluation)
      have restRecursiveTotal :
          ∃ result,
            grammar.Evaluates
              (.sequence
                (.nonterminal entryName)
                (.nonterminal restName))
              input result :=
        sequence_total_of_success_shorter
          entryTotal
          (fun _ evaluation =>
            entry_success_length_lt evaluation)
          (fun smaller short =>
            smallerExpression
              (.nonterminal restName) smaller short)
      have restBodyTotal :
          ∃ result, grammar.Evaluates restRule input result := by
        change
          ∃ result,
            grammar.Evaluates
              (.orderedChoice
                (.sequence
                  (.nonterminal entryName)
                  (.nonterminal restName))
                .empty)
              input result
        exact orderedChoice_total restRecursiveTotal
          ⟨.success input, .empty input⟩
      have restTotal : CallTotal restName input :=
        restBodyTotal.imp fun _ evaluation =>
          .nonterminal (by simpa using evaluation)
      have m0ZeroTotal :
          ∃ result,
            grammar.Evaluates
              (.sequence
                (.terminal .bit0)
                (.sequence
                  (.nonterminal m0Name)
                  (.nonterminal bitName)))
              input result :=
        sequence_total_of_success_shorter
          (terminal_total .bit0 input)
          (fun _ evaluation =>
            terminal_success_length_lt evaluation)
          (fun smaller short =>
            smallerExpression _ smaller short)
      have m0OneTotal :
          ∃ result,
            grammar.Evaluates
              (.sequence
                (.terminal .bit1)
                (.orderedChoice
                  (.sequence
                    (.nonterminal m0Name)
                    (.terminal .bit0))
                  (.sequence
                    (.nonterminal m1Name)
                    (.terminal .bit1))))
              input result :=
        sequence_total_of_success_shorter
          (terminal_total .bit1 input)
          (fun _ evaluation =>
            terminal_success_length_lt evaluation)
          (fun smaller short =>
            smallerExpression _ smaller short)
      have m0EndTotal :
          ∃ result,
            grammar.Evaluates
              (.sequence
                (.terminal .rangle)
                (.sequence
                  (.nonterminal restName)
                  (.terminal .dollar)))
              input result :=
        sequence_total_of_success_shorter
          (terminal_total .rangle input)
          (fun _ evaluation =>
            terminal_success_length_lt evaluation)
          (fun smaller short =>
            smallerExpression _ smaller short)
      have m0BodyTotal :
          ∃ result, grammar.Evaluates m0Rule input result := by
        change
          ∃ result,
            grammar.Evaluates
              (.orderedChoice
                (.sequence
                  (.terminal .bit0)
                  (.sequence
                    (.nonterminal m0Name)
                    (.nonterminal bitName)))
                (.orderedChoice
                  (.sequence
                    (.terminal .bit1)
                    (.orderedChoice
                      (.sequence
                        (.nonterminal m0Name)
                        (.terminal .bit0))
                      (.sequence
                        (.nonterminal m1Name)
                        (.terminal .bit1))))
                  (.sequence
                    (.terminal .rangle)
                    (.sequence
                      (.nonterminal restName)
                      (.terminal .dollar)))))
              input result
        exact orderedChoice_total m0ZeroTotal
          (orderedChoice_total m0OneTotal m0EndTotal)
      have m0Total : CallTotal m0Name input :=
        m0BodyTotal.imp fun _ evaluation =>
          .nonterminal (by simpa using evaluation)
      have m1ZeroTotal :
          ∃ result,
            grammar.Evaluates
              (.sequence
                (.terminal .bit0)
                (.sequence
                  (.nonterminal m1Name)
                  (.nonterminal bitName)))
              input result :=
        sequence_total_of_success_shorter
          (terminal_total .bit0 input)
          (fun _ evaluation =>
            terminal_success_length_lt evaluation)
          (fun smaller short =>
            smallerExpression _ smaller short)
      have m1OneTotal :
          ∃ result,
            grammar.Evaluates
              (.sequence
                (.terminal .bit1)
                (.orderedChoice
                  (.sequence
                    (.nonterminal m1Name)
                    (.terminal .bit0))
                  (.sequence
                    (.nonterminal m0Name)
                    (.terminal .bit1))))
              input result :=
        sequence_total_of_success_shorter
          (terminal_total .bit1 input)
          (fun _ evaluation =>
            terminal_success_length_lt evaluation)
          (fun smaller short =>
            smallerExpression _ smaller short)
      have m1BodyTotal :
          ∃ result, grammar.Evaluates m1Rule input result := by
        change
          ∃ result,
            grammar.Evaluates
              (.orderedChoice
                (.sequence
                  (.terminal .bit0)
                  (.sequence
                    (.nonterminal m1Name)
                    (.nonterminal bitName)))
                (.sequence
                  (.terminal .bit1)
                  (.orderedChoice
                    (.sequence
                      (.nonterminal m1Name)
                      (.terminal .bit0))
                    (.sequence
                      (.nonterminal m0Name)
                      (.terminal .bit1)))))
              input result
        exact orderedChoice_total m1ZeroTotal m1OneTotal
      have m1Total : CallTotal m1Name input :=
        m1BodyTotal.imp fun _ evaluation =>
          .nonterminal (by simpa using evaluation)
      have keyZeroTotal :
          ∃ result,
            grammar.Evaluates
              (.sequence
                (.terminal .bit0)
                (.sequence
                  (.nonterminal keyName)
                  (.terminal .bit0)))
              input result :=
        sequence_total_of_success_shorter
          (terminal_total .bit0 input)
          (fun _ evaluation =>
            terminal_success_length_lt evaluation)
          (fun smaller short =>
            smallerExpression _ smaller short)
      have keyOneTotal :
          ∃ result,
            grammar.Evaluates
              (.sequence
                (.terminal .bit1)
                (.sequence
                  (.nonterminal keyName)
                  (.terminal .bit1)))
              input result :=
        sequence_total_of_success_shorter
          (terminal_total .bit1 input)
          (fun _ evaluation =>
            terminal_success_length_lt evaluation)
          (fun smaller short =>
            smallerExpression _ smaller short)
      have keyEndTotal :
          ∃ result,
            grammar.Evaluates
              (.sequence
                (.terminal .colon)
                (.sequence
                  (.nonterminal m1Name)
                  (.terminal .hash)))
              input result :=
        sequence_total_of_success_shorter
          (terminal_total .colon input)
          (fun _ evaluation =>
            terminal_success_length_lt evaluation)
          (fun smaller short =>
            smallerExpression _ smaller short)
      have keyBodyTotal :
          ∃ result, grammar.Evaluates keyRule input result := by
        change
          ∃ result,
            grammar.Evaluates
              (.orderedChoice
                (.sequence
                  (.terminal .bit0)
                  (.sequence
                    (.nonterminal keyName)
                    (.terminal .bit0)))
                (.orderedChoice
                  (.sequence
                    (.terminal .bit1)
                    (.sequence
                      (.nonterminal keyName)
                      (.terminal .bit1)))
                  (.sequence
                    (.terminal .colon)
                    (.sequence
                      (.nonterminal m1Name)
                      (.terminal .hash)))))
              input result
        exact orderedChoice_total keyZeroTotal
          (orderedChoice_total keyOneTotal keyEndTotal)
      have keyTotal : CallTotal keyName input :=
        keyBodyTotal.imp fun _ evaluation =>
          .nonterminal (by simpa using evaluation)
      have anyTerminalTotal :
          ∃ result, grammar.Evaluates anyTerminal input result := by
        change
          ∃ result,
            grammar.Evaluates
              (.orderedChoice (.terminal .bit0)
                (.orderedChoice (.terminal .bit1)
                  (.orderedChoice (.terminal .langle)
                    (.orderedChoice (.terminal .colon)
                      (.orderedChoice (.terminal .rangle)
                        (.orderedChoice
                          (.terminal .dollar)
                          (.terminal .hash)))))))
              input result
        exact orderedChoice_total
          (terminal_total .bit0 input)
          (orderedChoice_total
            (terminal_total .bit1 input)
            (orderedChoice_total
              (terminal_total .langle input)
              (orderedChoice_total
                (terminal_total .colon input)
                (orderedChoice_total
                  (terminal_total .rangle input)
                  (orderedChoice_total
                    (terminal_total .dollar input)
                    (terminal_total .hash input))))))
      have endBodyTotal :
          ∃ result, grammar.Evaluates endRule input result :=
        notPredicate_total anyTerminalTotal
      have endTotal : CallTotal endName input :=
        endBodyTotal.imp fun _ evaluation =>
          .nonterminal (by simpa using evaluation)
      have hitBodyTotal :
          ∃ result, grammar.Evaluates hitRule input result := by
        change
          ∃ result,
            grammar.Evaluates
              (.sequence
                (.terminal .langle)
                (.sequence
                  (.orderedChoice
                    (.sequence
                      (.terminal .bit0)
                      (.sequence
                        (.nonterminal keyName)
                        (.terminal .bit0)))
                    (.sequence
                      (.terminal .bit1)
                      (.sequence
                        (.nonterminal keyName)
                        (.terminal .bit1))))
                  (.nonterminal endName)))
              input result
        exact sequence_total_of_success_shorter
          (terminal_total .langle input)
          (fun _ evaluation =>
            terminal_success_length_lt evaluation)
          (fun smaller short =>
            smallerExpression _ smaller short)
      have hitTotal : CallTotal hitName input :=
        hitBodyTotal.imp fun _ evaluation =>
          .nonterminal (by simpa using evaluation)
      have searchRecursiveTotal :
          ∃ result,
            grammar.Evaluates
              (.sequence
                (.nonterminal entryName)
                (.nonterminal searchName))
              input result :=
        sequence_total_of_success_shorter
          entryTotal
          (fun _ evaluation =>
            entry_success_length_lt evaluation)
          (fun smaller short =>
            smallerExpression
              (.nonterminal searchName) smaller short)
      have searchBodyTotal :
          ∃ result, grammar.Evaluates searchRule input result := by
        change
          ∃ result,
            grammar.Evaluates
              (.orderedChoice
                (.nonterminal hitName)
                (.sequence
                  (.nonterminal entryName)
                  (.nonterminal searchName)))
              input result
        exact orderedChoice_total hitTotal searchRecursiveTotal
      have searchTotal : CallTotal searchName input :=
        searchBodyTotal.imp fun _ evaluation =>
          .nonterminal (by simpa using evaluation)
      intro currentName
      fin_cases currentName
      · simpa [bitName] using bitTotal
      · simpa [bitsName] using bitsTotal
      · simpa [entryName] using entryTotal
      · simpa [restName] using restTotal
      · simpa [m0Name] using m0Total
      · simpa [m1Name] using m1Total
      · simpa [keyName] using keyTotal
      · simpa [endName] using endTotal
      · simpa [hitName] using hitTotal
      · simpa [searchName] using searchTotal
  exact bounded input.length input rfl name

theorem grammar_isLoffTotal :
    grammar.IsLoffTotal := by
  apply loffTotal_of_nonterminal_total
  exact nonterminal_call_total

end PegSeparation.Witness.DirectPEG
