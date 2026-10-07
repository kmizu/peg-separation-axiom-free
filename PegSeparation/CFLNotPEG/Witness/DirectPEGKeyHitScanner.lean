import PegSeparation.CFLNotPEG.Witness.DirectPEGRecordScanners
import PegSeparation.CFLNotPEG.Witness.DirectPEGParityScanner


namespace PegSeparation.Witness.DirectPEG

open PegSeparation

namespace KeyHitScanner

def KeyResidual (input remaining : Word) : Prop :=
  ∃ word : Word,
    LanguageCFG.Grammar.K word ∧ input = word ++ remaining

def WitnessResidual (input remaining : Word) : Prop :=
  LanguageCFG.Grammar.A input ∧ remaining = []

private theorem terminal_success
    {symbol : Terminal} {input remaining : Word}
    (evaluation :
      grammar.Evaluates (.terminal symbol) input (.success remaining)) :
    input = symbol :: remaining := by
  have resultEquation :=
    PegSeparation.External.LoffForwardRepaired.PegGrammar.evaluates_deterministic
      evaluation
      (PegGrammar.Evaluates.terminal
        (grammar := grammar) symbol input)
  cases input with
  | nil =>
      simp [PegGrammar.terminalResult] at resultEquation
  | cons actual rest =>
      simp only [PegGrammar.terminalResult] at resultEquation
      split at resultEquation
      · rename_i same
        subst actual
        simpa using resultEquation.symm
      · simp at resultEquation

private theorem evaluates_terminal_match
    (symbol : Terminal) (remaining : Word) :
    grammar.Evaluates
      (.terminal symbol) (symbol :: remaining) (.success remaining) := by
  simpa [PegGrammar.terminalResult] using
    (PegGrammar.Evaluates.terminal
      (grammar := grammar) symbol (symbol :: remaining))

private theorem evaluates_terminal_mismatch
    {wanted actual : Terminal} (different : actual ≠ wanted)
    (remaining : Word) :
    grammar.Evaluates (.terminal wanted) (actual :: remaining) .failure := by
  simpa [PegGrammar.terminalResult, different] using
    (PegGrammar.Evaluates.terminal
      (grammar := grammar) wanted (actual :: remaining))

private theorem evaluates_terminal_nil (symbol : Terminal) :
    grammar.Evaluates (.terminal symbol) [] .failure := by
  simpa [PegGrammar.terminalResult] using
    (PegGrammar.Evaluates.terminal (grammar := grammar) symbol [])

theorem key_success_sound
    {input remaining : Word}
    (evaluation :
      grammar.Evaluates
        (.nonterminal keyName) input (.success remaining)) :
    KeyResidual input remaining := by
  cases evaluation with
  | nonterminal body =>
      rw [grammar_rule_key] at body
      cases body with
      | choiceLeft zero =>
          cases zero with
          | sequenceSuccess zeroOpening zeroTail =>
              cases zeroTail with
              | sequenceSuccess recursive zeroClosing =>
                  have zeroOpeningEquation :=
                    terminal_success zeroOpening
                  have zeroClosingEquation :=
                    terminal_success zeroClosing
                  rcases key_success_sound recursive with
                    ⟨word, derivation, recursiveInputEquation⟩
                  refine
                    ⟨.bit0 :: (word ++ [.bit0]),
                      LanguageCFG.Grammar.K.wrapZero derivation, ?_⟩
                  rw [zeroOpeningEquation, recursiveInputEquation,
                    zeroClosingEquation]
                  simp
      | choiceRight _ rest =>
          cases rest with
          | choiceLeft one =>
              cases one with
              | sequenceSuccess oneOpening oneTail =>
                  cases oneTail with
                  | sequenceSuccess recursive oneClosing =>
                      have oneOpeningEquation :=
                        terminal_success oneOpening
                      have oneClosingEquation :=
                        terminal_success oneClosing
                      rcases key_success_sound recursive with
                        ⟨word, derivation, recursiveInputEquation⟩
                      refine
                        ⟨.bit1 :: (word ++ [.bit1]),
                          LanguageCFG.Grammar.K.wrapOne derivation, ?_⟩
                      rw [oneOpeningEquation, recursiveInputEquation,
                        oneClosingEquation]
                      simp
          | choiceRight _ base =>
              cases base with
              | sequenceSuccess colonOpening baseTail =>
                  cases baseTail with
                  | sequenceSuccess parity hashClosing =>
                      have colonOpeningEquation :=
                        terminal_success colonOpening
                      have hashClosingEquation :=
                        terminal_success hashClosing
                      rcases Correctness.m_success_sound true parity with
                        ⟨word, derivation, parityInputEquation⟩
                      refine
                        ⟨[.colon] ++ word ++ [.hash],
                          LanguageCFG.Grammar.K.base derivation, ?_⟩
                      rw [colonOpeningEquation, parityInputEquation,
                        hashClosingEquation]
                      simp

theorem key_complete
    {word : Word} (derivation : LanguageCFG.Grammar.K word)
    (remaining : Word) :
    grammar.Evaluates
      (.nonterminal keyName) (word ++ remaining) (.success remaining) := by
  induction derivation generalizing remaining with
  | @base middleWord parity =>
      have parityEvaluation :=
        Correctness.m_success_complete parity (.hash :: remaining)
      apply PegGrammar.Evaluates.nonterminal
      simp only [grammar_rule_key, keyRule]
      change grammar.Evaluates
        (.orderedChoice
          (.sequence (.terminal .bit0)
            (.sequence (.nonterminal keyName) (.terminal .bit0)))
          (.orderedChoice
            (.sequence (.terminal .bit1)
              (.sequence (.nonterminal keyName) (.terminal .bit1)))
            (.sequence (.terminal .colon)
              (.sequence (.nonterminal m1Name) (.terminal .hash)))))
        _ _
      simpa [List.append_assoc] using
        (PegGrammar.Evaluates.choiceRight
          (PegGrammar.Evaluates.sequenceFailure
            (evaluates_terminal_mismatch (by decide)
              (middleWord ++ .hash :: remaining)))
          (PegGrammar.Evaluates.choiceRight
            (PegGrammar.Evaluates.sequenceFailure
              (evaluates_terminal_mismatch (by decide)
                (middleWord ++ .hash :: remaining)))
            (PegGrammar.Evaluates.sequenceSuccess
              (evaluates_terminal_match .colon
                (middleWord ++ .hash :: remaining))
              (PegGrammar.Evaluates.sequenceSuccess parityEvaluation
                (evaluates_terminal_match .hash remaining)))))
  | @wrapZero nestedWord nested inductionHypothesis =>
      have recursiveEvaluation :=
        inductionHypothesis (.bit0 :: remaining)
      apply PegGrammar.Evaluates.nonterminal
      simp only [grammar_rule_key, keyRule]
      change grammar.Evaluates
        (.orderedChoice
          (.sequence (.terminal .bit0)
            (.sequence (.nonterminal keyName) (.terminal .bit0)))
          (.orderedChoice
            (.sequence (.terminal .bit1)
              (.sequence (.nonterminal keyName) (.terminal .bit1)))
            (.sequence (.terminal .colon)
              (.sequence (.nonterminal m1Name) (.terminal .hash)))))
        _ _
      simpa [List.append_assoc] using
        (PegGrammar.Evaluates.choiceLeft
          (PegGrammar.Evaluates.sequenceSuccess
            (evaluates_terminal_match .bit0
              (nestedWord ++ .bit0 :: remaining))
            (PegGrammar.Evaluates.sequenceSuccess recursiveEvaluation
              (evaluates_terminal_match .bit0 remaining))))
  | @wrapOne nestedWord nested inductionHypothesis =>
      have recursiveEvaluation :=
        inductionHypothesis (.bit1 :: remaining)
      apply PegGrammar.Evaluates.nonterminal
      simp only [grammar_rule_key, keyRule]
      change grammar.Evaluates
        (.orderedChoice
          (.sequence (.terminal .bit0)
            (.sequence (.nonterminal keyName) (.terminal .bit0)))
          (.orderedChoice
            (.sequence (.terminal .bit1)
              (.sequence (.nonterminal keyName) (.terminal .bit1)))
            (.sequence (.terminal .colon)
              (.sequence (.nonterminal m1Name) (.terminal .hash)))))
        _ _
      simpa [List.append_assoc] using
        (PegGrammar.Evaluates.choiceRight
          (PegGrammar.Evaluates.sequenceFailure
            (evaluates_terminal_mismatch (by decide)
              (nestedWord ++ .bit1 :: remaining)))
          (PegGrammar.Evaluates.choiceLeft
            (PegGrammar.Evaluates.sequenceSuccess
              (evaluates_terminal_match .bit1
                (nestedWord ++ .bit1 :: remaining))
              (PegGrammar.Evaluates.sequenceSuccess recursiveEvaluation
                (evaluates_terminal_match .bit1 remaining)))))

theorem key_success_iff
    {input remaining : Word} :
    grammar.Evaluates
        (.nonterminal keyName) input (.success remaining) ↔
      KeyResidual input remaining := by
  constructor
  · exact key_success_sound
  · rintro ⟨word, derivation, rfl⟩
    exact key_complete derivation remaining

private theorem anyTerminal_fails_on_nil :
    grammar.Evaluates anyTerminal [] .failure := by
  exact .choiceRight
    (evaluates_terminal_nil .bit0)
    (.choiceRight
      (evaluates_terminal_nil .bit1)
      (.choiceRight
        (evaluates_terminal_nil .langle)
        (.choiceRight
          (evaluates_terminal_nil .colon)
          (.choiceRight
            (evaluates_terminal_nil .rangle)
            (.choiceRight
              (evaluates_terminal_nil .dollar)
              (evaluates_terminal_nil .hash))))))

private theorem end_complete :
    grammar.Evaluates (.nonterminal endName) [] (.success []) := by
  apply PegGrammar.Evaluates.nonterminal
  rw [grammar_rule_end]
  exact .notSuccess anyTerminal_fails_on_nil

private theorem anyTerminal_succeeds_on_cons
    (symbol : Terminal) (remaining : Word) :
    ∃ rest,
      grammar.Evaluates anyTerminal (symbol :: remaining) (.success rest) := by
  cases symbol with
  | bit0 =>
      exact ⟨remaining, .choiceLeft
        (evaluates_terminal_match .bit0 remaining)⟩
  | bit1 =>
      exact ⟨remaining, .choiceRight
        (evaluates_terminal_mismatch (by decide) remaining)
        (.choiceLeft (evaluates_terminal_match .bit1 remaining))⟩
  | langle =>
      exact ⟨remaining, .choiceRight
        (evaluates_terminal_mismatch (by decide) remaining)
        (.choiceRight
          (evaluates_terminal_mismatch (by decide) remaining)
          (.choiceLeft (evaluates_terminal_match .langle remaining)))⟩
  | colon =>
      exact ⟨remaining, .choiceRight
        (evaluates_terminal_mismatch (by decide) remaining)
        (.choiceRight
          (evaluates_terminal_mismatch (by decide) remaining)
          (.choiceRight
            (evaluates_terminal_mismatch (by decide) remaining)
            (.choiceLeft (evaluates_terminal_match .colon remaining))))⟩
  | rangle =>
      exact ⟨remaining, .choiceRight
        (evaluates_terminal_mismatch (by decide) remaining)
        (.choiceRight
          (evaluates_terminal_mismatch (by decide) remaining)
          (.choiceRight
            (evaluates_terminal_mismatch (by decide) remaining)
            (.choiceRight
              (evaluates_terminal_mismatch (by decide) remaining)
              (.choiceLeft
                (evaluates_terminal_match .rangle remaining)))))⟩
  | dollar =>
      exact ⟨remaining, .choiceRight
        (evaluates_terminal_mismatch (by decide) remaining)
        (.choiceRight
          (evaluates_terminal_mismatch (by decide) remaining)
          (.choiceRight
            (evaluates_terminal_mismatch (by decide) remaining)
            (.choiceRight
              (evaluates_terminal_mismatch (by decide) remaining)
              (.choiceRight
                (evaluates_terminal_mismatch (by decide) remaining)
                (.choiceLeft
                  (evaluates_terminal_match .dollar remaining))))))⟩
  | hash =>
      exact ⟨remaining, .choiceRight
        (evaluates_terminal_mismatch (by decide) remaining)
        (.choiceRight
          (evaluates_terminal_mismatch (by decide) remaining)
          (.choiceRight
            (evaluates_terminal_mismatch (by decide) remaining)
            (.choiceRight
              (evaluates_terminal_mismatch (by decide) remaining)
              (.choiceRight
                (evaluates_terminal_mismatch (by decide) remaining)
                (.choiceRight
                  (evaluates_terminal_mismatch (by decide) remaining)
                  (evaluates_terminal_match .hash remaining))))))⟩

theorem end_success_nil
    {input remaining : Word}
    (evaluation :
      grammar.Evaluates
        (.nonterminal endName) input (.success remaining)) :
    input = [] ∧ remaining = [] := by
  cases evaluation with
  | nonterminal body =>
      rw [grammar_rule_end] at body
      cases body with
      | notSuccess anyFailure =>
          cases input with
          | nil => exact ⟨rfl, rfl⟩
          | cons symbol rest =>
              obtain ⟨after, anySuccess⟩ :=
                anyTerminal_succeeds_on_cons symbol rest
              have resultEquation :=
                PegSeparation.External.LoffForwardRepaired.PegGrammar.evaluates_deterministic
                  anyFailure anySuccess
              simp at resultEquation

def CurrentWitness (input : Word) : Prop :=
  ∃ bit : LanguageCFG.Bit, ∃ word : Word,
    LanguageCFG.Grammar.K word ∧
    input =
      .langle :: LanguageCFG.bitTerminal bit ::
        (word ++ [LanguageCFG.bitTerminal bit])

theorem hit_success_exact
    {input remaining : Word}
    (evaluation :
      grammar.Evaluates
        (.nonterminal hitName) input (.success remaining)) :
    CurrentWitness input ∧ remaining = [] := by
  cases evaluation with
  | nonterminal body =>
      rw [grammar_rule_hit] at body
      cases body with
      | sequenceSuccess opening tail =>
          cases tail with
          | sequenceSuccess witness endEvaluation =>
              have openingEquation := terminal_success opening
              rcases end_success_nil endEvaluation with
                ⟨endInputEquation, remainingEquation⟩
              cases witness with
              | choiceLeft zero =>
                  cases zero with
                  | sequenceSuccess zeroOpening zeroTail =>
                      cases zeroTail with
                      | sequenceSuccess key zeroClosing =>
                          have zeroOpeningEquation :=
                            terminal_success zeroOpening
                          have zeroClosingEquation :=
                            terminal_success zeroClosing
                          rcases key_success_sound key with
                            ⟨word, derivation, keyInputEquation⟩
                          refine
                            ⟨⟨false, word, derivation, ?_⟩,
                              remainingEquation⟩
                          simp only [LanguageCFG.bitTerminal]
                          rw [openingEquation, zeroOpeningEquation,
                            keyInputEquation, zeroClosingEquation,
                            endInputEquation]
              | choiceRight _ one =>
                  cases one with
                  | sequenceSuccess oneOpening oneTail =>
                      cases oneTail with
                      | sequenceSuccess key oneClosing =>
                          have oneOpeningEquation :=
                            terminal_success oneOpening
                          have oneClosingEquation :=
                            terminal_success oneClosing
                          rcases key_success_sound key with
                            ⟨word, derivation, keyInputEquation⟩
                          refine
                            ⟨⟨true, word, derivation, ?_⟩,
                              remainingEquation⟩
                          simp only [LanguageCFG.bitTerminal]
                          rw [openingEquation, oneOpeningEquation,
                            keyInputEquation, oneClosingEquation,
                            endInputEquation]

theorem hit_success_sound
    {input remaining : Word}
    (evaluation :
      grammar.Evaluates
        (.nonterminal hitName) input (.success remaining)) :
    WitnessResidual input remaining := by
  rcases hit_success_exact evaluation with
    ⟨⟨bit, word, derivation, rfl⟩, remainingEquation⟩
  refine ⟨?_, remainingEquation⟩
  cases bit
  · simpa [LanguageCFG.bitTerminal] using
      LanguageCFG.Grammar.A.witnessZero derivation
  · simpa [LanguageCFG.bitTerminal] using
      LanguageCFG.Grammar.A.witnessOne derivation

theorem hit_complete
    {input : Word} (witness : CurrentWitness input) :
    grammar.Evaluates
      (.nonterminal hitName) input (.success []) := by
  rcases witness with ⟨bit, word, derivation, rfl⟩
  apply PegGrammar.Evaluates.nonterminal
  cases bit
  · have keyEvaluation :=
      key_complete derivation [.bit0]
    have outerEvaluation :
        grammar.Evaluates
          (.orderedChoice
            (.sequence (.terminal .bit0)
              (.sequence (.nonterminal keyName) (.terminal .bit0)))
            (.sequence (.terminal .bit1)
              (.sequence (.nonterminal keyName) (.terminal .bit1))))
          (.bit0 :: (word ++ [.bit0])) (.success []) :=
      .choiceLeft
        (.sequenceSuccess
          (evaluates_terminal_match .bit0 (word ++ [.bit0]))
          (.sequenceSuccess keyEvaluation
            (evaluates_terminal_match .bit0 [])))
    simp only [grammar_rule_hit, hitRule]
    change grammar.Evaluates
      (.sequence (.terminal .langle)
        (.sequence
          (.orderedChoice
            (.sequence (.terminal .bit0)
              (.sequence (.nonterminal keyName) (.terminal .bit0)))
            (.sequence (.terminal .bit1)
              (.sequence (.nonterminal keyName) (.terminal .bit1))))
          (.nonterminal endName)))
      _ _
    simpa [LanguageCFG.bitTerminal] using
      (PegGrammar.Evaluates.sequenceSuccess
        (evaluates_terminal_match .langle
          (.bit0 :: (word ++ [.bit0])))
        (PegGrammar.Evaluates.sequenceSuccess
          outerEvaluation end_complete))
  · have keyEvaluation :=
      key_complete derivation [.bit1]
    have zeroFailure :
        grammar.Evaluates
          (.sequence (.terminal .bit0)
            (.sequence (.nonterminal keyName) (.terminal .bit0)))
          (.bit1 :: (word ++ [.bit1])) .failure :=
      .sequenceFailure
        (evaluates_terminal_mismatch (by decide) (word ++ [.bit1]))
    have oneEvaluation :
        grammar.Evaluates
          (.sequence (.terminal .bit1)
            (.sequence (.nonterminal keyName) (.terminal .bit1)))
          (.bit1 :: (word ++ [.bit1])) (.success []) :=
      .sequenceSuccess
        (evaluates_terminal_match .bit1 (word ++ [.bit1]))
        (.sequenceSuccess keyEvaluation
          (evaluates_terminal_match .bit1 []))
    have outerEvaluation :
        grammar.Evaluates
          (.orderedChoice
            (.sequence (.terminal .bit0)
              (.sequence (.nonterminal keyName) (.terminal .bit0)))
            (.sequence (.terminal .bit1)
              (.sequence (.nonterminal keyName) (.terminal .bit1))))
          (.bit1 :: (word ++ [.bit1])) (.success []) :=
      .choiceRight zeroFailure oneEvaluation
    simp only [grammar_rule_hit, hitRule]
    change grammar.Evaluates
      (.sequence (.terminal .langle)
        (.sequence
          (.orderedChoice
            (.sequence (.terminal .bit0)
              (.sequence (.nonterminal keyName) (.terminal .bit0)))
            (.sequence (.terminal .bit1)
              (.sequence (.nonterminal keyName) (.terminal .bit1))))
          (.nonterminal endName)))
      _ _
    simpa [LanguageCFG.bitTerminal] using
      (PegGrammar.Evaluates.sequenceSuccess
        (evaluates_terminal_match .langle
          (.bit1 :: (word ++ [.bit1])))
        (PegGrammar.Evaluates.sequenceSuccess
          outerEvaluation end_complete))

theorem hit_success_iff
    {input remaining : Word} :
    grammar.Evaluates
        (.nonterminal hitName) input (.success remaining) ↔
      CurrentWitness input ∧ remaining = [] := by
  constructor
  · exact hit_success_exact
  · rintro ⟨witness, rfl⟩
    exact hit_complete witness

end KeyHitScanner

end PegSeparation.Witness.DirectPEG
