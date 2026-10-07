import PegSeparation.CFLNotPEG.Witness.DirectPEGRecordScanners


namespace PegSeparation.Witness.DirectPEG

open PegSeparation

namespace Correctness

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

private theorem bit_evaluates
    (bit : LanguageCFG.Bit) (remaining : Word) :
    grammar.Evaluates
      (.nonterminal bitName)
      (LanguageCFG.bitTerminal bit :: remaining)
      (.success remaining) := by
  apply PegGrammar.Evaluates.nonterminal
  rw [grammar_rule_bit]
  cases bit
  · exact .choiceLeft (evaluates_terminal_match .bit0 remaining)
  · exact .choiceRight
      (evaluates_terminal_mismatch (by decide) remaining)
      (evaluates_terminal_match .bit1 remaining)

mutual

theorem m0_success_sound
    {input remaining : Word}
    (evaluation :
      grammar.Evaluates
        (.nonterminal m0Name) input (.success remaining)) :
    MResidual false input remaining := by
  cases evaluation with
  | nonterminal body =>
      rw [grammar_rule_m0] at body
      change grammar.Evaluates
        (.orderedChoice
          (.sequence (.terminal .bit0)
            (.sequence (.nonterminal m0Name) (.nonterminal bitName)))
          (.orderedChoice
            (.sequence (.terminal .bit1)
              (.orderedChoice
                (.sequence (.nonterminal m0Name) (.terminal .bit0))
                (.sequence (.nonterminal m1Name) (.terminal .bit1))))
            (.sequence (.terminal .rangle)
              (.sequence (.nonterminal restName) (.terminal .dollar)))))
        input (.success remaining) at body
      cases body with
      | choiceLeft zeroBranch =>
          cases zeroBranch with
          | sequenceSuccess opening tail =>
              cases tail with
              | sequenceSuccess recursive closing =>
                  have inputEquation := terminal_success opening
                  rcases m0_success_sound recursive with
                    ⟨word, derivation, recursiveEquation⟩
                  rcases bit_success_sound closing with
                    ⟨bit, closingEquation⟩
                  refine ⟨
                    LanguageCFG.bitTerminal false ::
                      (word ++ [LanguageCFG.bitTerminal bit]),
                    ?_, ?_⟩
                  · cases bit
                    · exact LanguageCFG.Grammar.P.zero00 derivation
                    · exact LanguageCFG.Grammar.P.zero01 derivation
                  · rw [inputEquation, recursiveEquation, closingEquation]
                    simp [LanguageCFG.bitTerminal, List.append_assoc]
      | choiceRight _ later =>
          cases later with
          | choiceLeft oneBranch =>
              cases oneBranch with
              | sequenceSuccess opening inner =>
                  have inputEquation := terminal_success opening
                  cases inner with
                  | choiceLeft zeroClosing =>
                      cases zeroClosing with
                      | sequenceSuccess recursive closing =>
                          rcases m0_success_sound recursive with
                            ⟨word, derivation, recursiveEquation⟩
                          have closingEquation := terminal_success closing
                          refine ⟨
                            LanguageCFG.bitTerminal true ::
                              (word ++ [LanguageCFG.bitTerminal false]),
                            LanguageCFG.Grammar.P.zero10 derivation, ?_⟩
                          rw [inputEquation, recursiveEquation, closingEquation]
                          simp [LanguageCFG.bitTerminal, List.append_assoc]
                  | choiceRight _ oneClosing =>
                      cases oneClosing with
                      | sequenceSuccess recursive closing =>
                          rcases m1_success_sound recursive with
                            ⟨word, derivation, recursiveEquation⟩
                          have closingEquation := terminal_success closing
                          refine ⟨
                            LanguageCFG.bitTerminal true ::
                              (word ++ [LanguageCFG.bitTerminal true]),
                            LanguageCFG.Grammar.P.zero11 derivation, ?_⟩
                          rw [inputEquation, recursiveEquation, closingEquation]
                          simp [LanguageCFG.bitTerminal, List.append_assoc]
          | choiceRight _ base =>
              cases base with
              | sequenceSuccess opening tail =>
                  cases tail with
                  | sequenceSuccess rest closing =>
                      have inputEquation := terminal_success opening
                      rcases rest_success_sound rest with
                        ⟨records, recordsValid, restEquation⟩
                      have closingEquation := terminal_success closing
                      refine ⟨
                        [.rangle] ++ LanguageCFG.recordsWord records ++
                          [.dollar],
                        LanguageCFG.Grammar.P.base
                          (LanguageCFG.Grammar.T.complete
                            records recordsValid),
                        ?_⟩
                      rw [inputEquation, restEquation, closingEquation]
                      simp [List.append_assoc]
termination_by input.length
decreasing_by
  all_goals
    rw [inputEquation]
    simp_wf

theorem m1_success_sound
    {input remaining : Word}
    (evaluation :
      grammar.Evaluates
        (.nonterminal m1Name) input (.success remaining)) :
    MResidual true input remaining := by
  cases evaluation with
  | nonterminal body =>
      rw [grammar_rule_m1] at body
      change grammar.Evaluates
        (.orderedChoice
          (.sequence (.terminal .bit0)
            (.sequence (.nonterminal m1Name) (.nonterminal bitName)))
          (.sequence (.terminal .bit1)
            (.orderedChoice
              (.sequence (.nonterminal m1Name) (.terminal .bit0))
              (.sequence (.nonterminal m0Name) (.terminal .bit1)))))
        input (.success remaining) at body
      cases body with
      | choiceLeft zeroBranch =>
          cases zeroBranch with
          | sequenceSuccess opening tail =>
              cases tail with
              | sequenceSuccess recursive closing =>
                  have inputEquation := terminal_success opening
                  rcases m1_success_sound recursive with
                    ⟨word, derivation, recursiveEquation⟩
                  rcases bit_success_sound closing with
                    ⟨bit, closingEquation⟩
                  refine ⟨
                    LanguageCFG.bitTerminal false ::
                      (word ++ [LanguageCFG.bitTerminal bit]),
                    ?_, ?_⟩
                  · cases bit
                    · exact LanguageCFG.Grammar.P.one00 derivation
                    · exact LanguageCFG.Grammar.P.one01 derivation
                  · rw [inputEquation, recursiveEquation, closingEquation]
                    simp [LanguageCFG.bitTerminal, List.append_assoc]
      | choiceRight _ oneBranch =>
          cases oneBranch with
          | sequenceSuccess opening inner =>
              have inputEquation := terminal_success opening
              cases inner with
              | choiceLeft zeroClosing =>
                  cases zeroClosing with
                  | sequenceSuccess recursive closing =>
                      rcases m1_success_sound recursive with
                        ⟨word, derivation, recursiveEquation⟩
                      have closingEquation := terminal_success closing
                      refine ⟨
                        LanguageCFG.bitTerminal true ::
                          (word ++ [LanguageCFG.bitTerminal false]),
                        LanguageCFG.Grammar.P.one10 derivation, ?_⟩
                      rw [inputEquation, recursiveEquation, closingEquation]
                      simp [LanguageCFG.bitTerminal, List.append_assoc]
              | choiceRight _ oneClosing =>
                  cases oneClosing with
                  | sequenceSuccess recursive closing =>
                      rcases m0_success_sound recursive with
                        ⟨word, derivation, recursiveEquation⟩
                      have closingEquation := terminal_success closing
                      refine ⟨
                        LanguageCFG.bitTerminal true ::
                          (word ++ [LanguageCFG.bitTerminal true]),
                        LanguageCFG.Grammar.P.one11 derivation, ?_⟩
                      rw [inputEquation, recursiveEquation, closingEquation]
                      simp [LanguageCFG.bitTerminal, List.append_assoc]
termination_by input.length
decreasing_by
  all_goals
    rw [inputEquation]
    simp_wf

end

theorem m_success_sound
    (parity : LanguageCFG.Bit) {input remaining : Word}
    (evaluation :
      grammar.Evaluates
        (.nonterminal (if parity then m1Name else m0Name))
        input (.success remaining)) :
    MResidual parity input remaining := by
  cases parity
  · exact m0_success_sound evaluation
  · exact m1_success_sound evaluation

private def mName (parity : LanguageCFG.Bit) : Fin 10 :=
  if parity then m1Name else m0Name

private theorem m_base_evaluates
    {word : Word} (derivation : LanguageCFG.Grammar.T word)
    (remaining : Word) :
    grammar.Evaluates
        (.nonterminal (mName false))
        (.rangle :: (word ++ .dollar :: remaining))
        (.success remaining) ∧
      grammar.Evaluates
        (.nonterminal (mName true))
        (.rangle :: (word ++ .dollar :: remaining))
        .failure := by
  rcases derivation.sound with ⟨records, valid, rfl⟩
  have rest :=
    rest_complete records (.dollar :: remaining) valid (by
      intro tail equality
      cases equality)
  have zeroFailure :=
    evaluates_terminal_mismatch
      (wanted := LanguageCFG.Terminal.bit0)
      (actual := LanguageCFG.Terminal.rangle)
      (by decide)
      (LanguageCFG.recordsWord records ++ .dollar :: remaining)
  have oneFailure :=
    evaluates_terminal_mismatch
      (wanted := LanguageCFG.Terminal.bit1)
      (actual := LanguageCFG.Terminal.rangle)
      (by decide)
      (LanguageCFG.recordsWord records ++ .dollar :: remaining)
  have close :=
    evaluates_terminal_match .rangle
      (LanguageCFG.recordsWord records ++ .dollar :: remaining)
  have dollar := evaluates_terminal_match .dollar remaining
  constructor
  · apply PegGrammar.Evaluates.nonterminal
    simp only [mName]
    exact .choiceRight
      (.sequenceFailure zeroFailure)
      (.choiceRight
        (.sequenceFailure oneFailure)
        (.sequenceSuccess close
          (.sequenceSuccess rest dollar)))
  · apply PegGrammar.Evaluates.nonterminal
    simp only [mName, if_true, grammar_rule_m1]
    exact .choiceRight
      (.sequenceFailure zeroFailure)
      (.sequenceFailure oneFailure)

private theorem m_step_zero
    (parity closingBit : LanguageCFG.Bit) {word : Word}
    (remaining : Word)
    (correct :
      grammar.Evaluates
        (.nonterminal (mName parity))
        (word ++ LanguageCFG.bitTerminal closingBit :: remaining)
        (.success (LanguageCFG.bitTerminal closingBit :: remaining)))
    (wrong :
      grammar.Evaluates
        (.nonterminal (mName (!parity)))
        (word ++ LanguageCFG.bitTerminal closingBit :: remaining)
        .failure) :
    grammar.Evaluates
        (.nonterminal (mName parity))
        (.bit0 ::
          (word ++ LanguageCFG.bitTerminal closingBit :: remaining))
        (.success remaining) ∧
      grammar.Evaluates
        (.nonterminal (mName (!parity)))
        (.bit0 ::
          (word ++ LanguageCFG.bitTerminal closingBit :: remaining))
        .failure := by
  have zero :=
    evaluates_terminal_match .bit0
      (word ++ LanguageCFG.bitTerminal closingBit :: remaining)
  have oneFailure :=
    evaluates_terminal_mismatch
      (wanted := LanguageCFG.Terminal.bit1)
      (actual := LanguageCFG.Terminal.bit0)
      (by decide)
      (word ++ LanguageCFG.bitTerminal closingBit :: remaining)
  have closeFailure :=
    evaluates_terminal_mismatch
      (wanted := LanguageCFG.Terminal.rangle)
      (actual := LanguageCFG.Terminal.bit0)
      (by decide)
      (word ++ LanguageCFG.bitTerminal closingBit :: remaining)
  have last := bit_evaluates closingBit remaining
  cases parity
  · constructor
    · apply PegGrammar.Evaluates.nonterminal
      simp only [mName]
      exact .choiceLeft
        (.sequenceSuccess zero
          (.sequenceSuccess correct last))
    · apply PegGrammar.Evaluates.nonterminal
      simp only [Bool.not_false, mName, if_true, grammar_rule_m1]
      exact .choiceRight
        (.sequenceSuccess zero (.sequenceFailure wrong))
        (.sequenceFailure oneFailure)
  · constructor
    · apply PegGrammar.Evaluates.nonterminal
      simp only [mName, if_true, grammar_rule_m1]
      exact .choiceLeft
        (.sequenceSuccess zero
          (.sequenceSuccess correct last))
    · apply PegGrammar.Evaluates.nonterminal
      simp only [Bool.not_true, mName]
      exact .choiceRight
        (.sequenceSuccess zero (.sequenceFailure wrong))
        (.choiceRight
          (.sequenceFailure oneFailure)
          (.sequenceFailure closeFailure))

private theorem m_step_one_zero
    (parity : LanguageCFG.Bit) {word : Word} (remaining : Word)
    (correct :
      grammar.Evaluates
        (.nonterminal (mName parity))
        (word ++ .bit0 :: remaining)
        (.success (.bit0 :: remaining)))
    (wrong :
      grammar.Evaluates
        (.nonterminal (mName (!parity)))
        (word ++ .bit0 :: remaining)
        .failure) :
    grammar.Evaluates
        (.nonterminal (mName parity))
        (.bit1 :: (word ++ .bit0 :: remaining))
        (.success remaining) ∧
      grammar.Evaluates
        (.nonterminal (mName (!parity)))
        (.bit1 :: (word ++ .bit0 :: remaining))
        .failure := by
  have zeroFailure :=
    evaluates_terminal_mismatch
      (wanted := LanguageCFG.Terminal.bit0)
      (actual := LanguageCFG.Terminal.bit1)
      (by decide) (word ++ .bit0 :: remaining)
  have one :=
    evaluates_terminal_match .bit1 (word ++ .bit0 :: remaining)
  have lastZero := evaluates_terminal_match .bit0 remaining
  have lastOneFailure :=
    evaluates_terminal_mismatch
      (wanted := LanguageCFG.Terminal.bit1)
      (actual := LanguageCFG.Terminal.bit0)
      (by decide) remaining
  have closeFailure :=
    evaluates_terminal_mismatch
      (wanted := LanguageCFG.Terminal.rangle)
      (actual := LanguageCFG.Terminal.bit1)
      (by decide) (word ++ .bit0 :: remaining)
  cases parity
  · constructor
    · apply PegGrammar.Evaluates.nonterminal
      simp only [mName]
      exact .choiceRight
        (.sequenceFailure zeroFailure)
        (.choiceLeft
          (.sequenceSuccess one
            (.choiceLeft
              (.sequenceSuccess correct lastZero))))
    · apply PegGrammar.Evaluates.nonterminal
      simp only [Bool.not_false, mName, if_true, grammar_rule_m1]
      exact .choiceRight
        (.sequenceFailure zeroFailure)
        (.sequenceSuccess one
          (.choiceRight
            (.sequenceFailure wrong)
            (.sequenceSuccess correct lastOneFailure)))
  · constructor
    · apply PegGrammar.Evaluates.nonterminal
      simp only [mName, if_true, grammar_rule_m1]
      exact .choiceRight
        (.sequenceFailure zeroFailure)
        (.sequenceSuccess one
          (.choiceLeft
            (.sequenceSuccess correct lastZero)))
    · apply PegGrammar.Evaluates.nonterminal
      simp only [Bool.not_true, mName]
      exact .choiceRight
        (.sequenceFailure zeroFailure)
        (.choiceRight
          (.sequenceSuccess one
            (.choiceRight
              (.sequenceFailure wrong)
              (.sequenceSuccess correct lastOneFailure)))
          (.sequenceFailure closeFailure))

private theorem m_step_one_one
    (parity : LanguageCFG.Bit) {word : Word} (remaining : Word)
    (correct :
      grammar.Evaluates
        (.nonterminal (mName parity))
        (word ++ .bit1 :: remaining)
        (.success (.bit1 :: remaining)))
    (wrong :
      grammar.Evaluates
        (.nonterminal (mName (!parity)))
        (word ++ .bit1 :: remaining)
        .failure) :
    grammar.Evaluates
        (.nonterminal (mName (!parity)))
        (.bit1 :: (word ++ .bit1 :: remaining))
        (.success remaining) ∧
      grammar.Evaluates
        (.nonterminal (mName parity))
        (.bit1 :: (word ++ .bit1 :: remaining))
        .failure := by
  have zeroFailure :=
    evaluates_terminal_mismatch
      (wanted := LanguageCFG.Terminal.bit0)
      (actual := LanguageCFG.Terminal.bit1)
      (by decide) (word ++ .bit1 :: remaining)
  have one :=
    evaluates_terminal_match .bit1 (word ++ .bit1 :: remaining)
  have lastZeroFailure :=
    evaluates_terminal_mismatch
      (wanted := LanguageCFG.Terminal.bit0)
      (actual := LanguageCFG.Terminal.bit1)
      (by decide) remaining
  have lastOne := evaluates_terminal_match .bit1 remaining
  have closeFailure :=
    evaluates_terminal_mismatch
      (wanted := LanguageCFG.Terminal.rangle)
      (actual := LanguageCFG.Terminal.bit1)
      (by decide) (word ++ .bit1 :: remaining)
  cases parity
  · constructor
    · apply PegGrammar.Evaluates.nonterminal
      simp only [Bool.not_false, mName, if_true, grammar_rule_m1]
      exact .choiceRight
        (.sequenceFailure zeroFailure)
        (.sequenceSuccess one
          (.choiceRight
            (.sequenceFailure wrong)
            (.sequenceSuccess correct lastOne)))
    · apply PegGrammar.Evaluates.nonterminal
      simp only [mName]
      exact .choiceRight
        (.sequenceFailure zeroFailure)
        (.choiceRight
          (.sequenceSuccess one
            (.choiceRight
              (.sequenceSuccess correct lastZeroFailure)
              (.sequenceFailure wrong)))
          (.sequenceFailure closeFailure))
  · constructor
    · apply PegGrammar.Evaluates.nonterminal
      simp only [Bool.not_true, mName]
      exact .choiceRight
        (.sequenceFailure zeroFailure)
        (.choiceLeft
          (.sequenceSuccess one
            (.choiceRight
              (.sequenceFailure wrong)
              (.sequenceSuccess correct lastOne))))
    · apply PegGrammar.Evaluates.nonterminal
      simp only [mName, if_true, grammar_rule_m1]
      exact .choiceRight
        (.sequenceFailure zeroFailure)
        (.sequenceSuccess one
          (.choiceRight
            (.sequenceSuccess correct lastZeroFailure)
            (.sequenceFailure wrong)))

private theorem m_parity_evaluates
    {parity : LanguageCFG.Bit} {word : Word}
    (derivation : LanguageCFG.Grammar.P parity word)
    (remaining : Word) :
    grammar.Evaluates
        (.nonterminal (mName parity))
        (word ++ remaining)
        (.success remaining) ∧
      grammar.Evaluates
        (.nonterminal (mName (!parity)))
        (word ++ remaining)
        .failure := by
  induction derivation generalizing remaining with
  | base restDerivation =>
      simpa [mName, List.append_assoc] using
        m_base_evaluates restDerivation remaining
  | zero00 _ inductionHypothesis =>
      simpa [mName, LanguageCFG.bitTerminal, List.append_assoc] using
        m_step_zero false false remaining
          (inductionHypothesis (.bit0 :: remaining)).1
          (inductionHypothesis (.bit0 :: remaining)).2
  | zero01 _ inductionHypothesis =>
      simpa [mName, LanguageCFG.bitTerminal, List.append_assoc] using
        m_step_zero false true remaining
          (inductionHypothesis (.bit1 :: remaining)).1
          (inductionHypothesis (.bit1 :: remaining)).2
  | zero10 _ inductionHypothesis =>
      simpa [mName, LanguageCFG.bitTerminal, List.append_assoc] using
        m_step_one_zero false remaining
          (inductionHypothesis (.bit0 :: remaining)).1
          (inductionHypothesis (.bit0 :: remaining)).2
  | zero11 _ inductionHypothesis =>
      simpa [mName, LanguageCFG.bitTerminal, List.append_assoc] using
        m_step_one_one true remaining
          (inductionHypothesis (.bit1 :: remaining)).1
          (inductionHypothesis (.bit1 :: remaining)).2
  | one00 _ inductionHypothesis =>
      simpa [mName, LanguageCFG.bitTerminal, List.append_assoc] using
        m_step_zero true false remaining
          (inductionHypothesis (.bit0 :: remaining)).1
          (inductionHypothesis (.bit0 :: remaining)).2
  | one01 _ inductionHypothesis =>
      simpa [mName, LanguageCFG.bitTerminal, List.append_assoc] using
        m_step_zero true true remaining
          (inductionHypothesis (.bit1 :: remaining)).1
          (inductionHypothesis (.bit1 :: remaining)).2
  | one10 _ inductionHypothesis =>
      simpa [mName, List.append_assoc] using
        m_step_one_zero true remaining
          (inductionHypothesis (.bit0 :: remaining)).1
          (inductionHypothesis (.bit0 :: remaining)).2
  | one11 _ inductionHypothesis =>
      simpa [mName, List.append_assoc] using
        m_step_one_one false remaining
          (inductionHypothesis (.bit1 :: remaining)).1
          (inductionHypothesis (.bit1 :: remaining)).2

theorem m_success_complete
    {parity : LanguageCFG.Bit} {word : Word}
    (derivation : LanguageCFG.Grammar.P parity word)
    (remaining : Word) :
    grammar.Evaluates
      (.nonterminal (if parity then m1Name else m0Name))
      (word ++ remaining) (.success remaining) := by
  simpa [mName] using (m_parity_evaluates derivation remaining).1

theorem m_opposite_failure
    {parity : LanguageCFG.Bit} {word : Word}
    (derivation : LanguageCFG.Grammar.P parity word)
    (remaining : Word) :
    grammar.Evaluates
      (.nonterminal (if !parity then m1Name else m0Name))
      (word ++ remaining) .failure := by
  simpa [mName] using (m_parity_evaluates derivation remaining).2

end Correctness

end PegSeparation.Witness.DirectPEG
