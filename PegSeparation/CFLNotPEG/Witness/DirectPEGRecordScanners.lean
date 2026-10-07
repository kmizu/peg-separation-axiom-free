import PegSeparation.CFLNotPEG.Witness.DirectPEG
import PegSeparation.Common.Loff.Semantics


namespace PegSeparation.Witness.DirectPEG

open PegSeparation

namespace Correctness

def BitResidual (input remaining : Word) : Prop :=
  ∃ bit : LanguageCFG.Bit,
    input = LanguageCFG.bitTerminal bit :: remaining

def BitsResidual (input remaining : Word) : Prop :=
  ∃ bits : List LanguageCFG.Bit,
    bits ≠ [] ∧ input = LanguageCFG.bitWord bits ++ remaining

def EntryResidual (input remaining : Word) : Prop :=
  ∃ record : LanguageCFG.Record,
    record.Valid ∧ input = LanguageCFG.recordWord record ++ remaining

def RestResidual (input remaining : Word) : Prop :=
  ∃ records : List LanguageCFG.Record,
    (∀ record ∈ records, record.Valid) ∧
    input = LanguageCFG.recordsWord records ++ remaining

def MResidual (parity : LanguageCFG.Bit)
    (input remaining : Word) : Prop :=
  ∃ word : Word,
    LanguageCFG.Grammar.P parity word ∧ input = word ++ remaining

def KResidual (input remaining : Word) : Prop :=
  ∃ word : Word,
    LanguageCFG.Grammar.K word ∧ input = word ++ remaining

def HitResidual (input remaining : Word) : Prop :=
  LanguageCFG.Grammar.A input ∧ remaining = []

def SearchResidual (input remaining : Word) : Prop :=
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

private theorem terminal_failure_match
    (symbol : Terminal) (remaining : Word) :
    grammar.Evaluates (.terminal symbol) (symbol :: remaining) .failure →
      False := by
  intro evaluation
  have resultEquation :=
    PegSeparation.External.LoffForwardRepaired.PegGrammar.evaluates_deterministic
      evaluation
      (PegGrammar.Evaluates.terminal
        (grammar := grammar) symbol (symbol :: remaining))
  simp [PegGrammar.terminalResult] at resultEquation

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

private def BitBoundary (input : Word) : Prop :=
  ∀ bit remaining,
    input ≠ LanguageCFG.bitTerminal bit :: remaining

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

private theorem bit_fails_at_boundary
    {input : Word} (boundary : BitBoundary input) :
    grammar.Evaluates (.nonterminal bitName) input .failure := by
  apply PegGrammar.Evaluates.nonterminal
  rw [grammar_rule_bit]
  cases input with
  | nil =>
      exact .choiceRight
        (evaluates_terminal_nil .bit0)
        (evaluates_terminal_nil .bit1)
  | cons head remaining =>
      have notZero : head ≠ .bit0 := by
        intro equality
        subst head
        exact boundary false remaining rfl
      have notOne : head ≠ .bit1 := by
        intro equality
        subst head
        exact boundary true remaining rfl
      exact .choiceRight
        (evaluates_terminal_mismatch notZero remaining)
        (evaluates_terminal_mismatch notOne remaining)

theorem bit_success_sound
    {input remaining : Word}
    (evaluation :
      grammar.Evaluates
        (.nonterminal bitName) input (.success remaining)) :
    BitResidual input remaining := by
  cases evaluation with
  | nonterminal body =>
      rw [grammar_rule_bit] at body
      cases body with
      | choiceLeft zero =>
          exact ⟨false, terminal_success zero⟩
      | choiceRight _ one =>
          exact ⟨true, terminal_success one⟩

theorem bits_success_sound
    {input remaining : Word}
    (evaluation :
      grammar.Evaluates
        (.nonterminal bitsName) input (.success remaining)) :
    BitsResidual input remaining := by
  cases evaluation with
  | nonterminal body =>
      rw [grammar_rule_bits] at body
      cases body with
      | choiceLeft recursive =>
          cases recursive with
          | sequenceSuccess first rest =>
              rcases bit_success_sound first with ⟨bit, inputEquation⟩
              rcases bits_success_sound rest with
                ⟨bits, bitsNonempty, restEquation⟩
              refine ⟨bit :: bits, by simp, ?_⟩
              rw [inputEquation]
              simp [restEquation, LanguageCFG.bitWord]
      | choiceRight _ one =>
          rcases bit_success_sound one with ⟨bit, rfl⟩
          exact ⟨[bit], by simp, by simp [LanguageCFG.bitWord]⟩
termination_by input.length
decreasing_by
  rw [inputEquation]
  simp_wf

private theorem bits_fails_at_boundary
    {input : Word} (boundary : BitBoundary input) :
    grammar.Evaluates (.nonterminal bitsName) input .failure := by
  have bitFailure := bit_fails_at_boundary boundary
  apply PegGrammar.Evaluates.nonterminal
  rw [grammar_rule_bits]
  exact .choiceRight (.sequenceFailure bitFailure) bitFailure

theorem bits_complete
    (bits : List LanguageCFG.Bit) (remaining : Word)
    (bitsNonempty : bits ≠ []) (boundary : BitBoundary remaining) :
    grammar.Evaluates
      (.nonterminal bitsName)
      (LanguageCFG.bitWord bits ++ remaining)
      (.success remaining) := by
  induction bits with
  | nil =>
      exact (bitsNonempty rfl).elim
  | cons bit bits inductionHypothesis =>
      cases bits with
      | nil =>
          have opening := bit_evaluates bit remaining
          have recursiveFailure := bits_fails_at_boundary boundary
          apply PegGrammar.Evaluates.nonterminal
          rw [grammar_rule_bits]
          change grammar.Evaluates
            (.orderedChoice
              (.sequence (.nonterminal bitName) (.nonterminal bitsName))
              (.nonterminal bitName))
            (LanguageCFG.bitTerminal bit :: remaining)
            (.success remaining)
          exact PegGrammar.Evaluates.choiceRight
              (PegGrammar.Evaluates.sequenceSuccess
                opening recursiveFailure)
              opening
      | cons next rest =>
          have tailNonempty : next :: rest ≠ [] := by simp
          have opening :=
            bit_evaluates bit
              (LanguageCFG.bitWord (next :: rest) ++ remaining)
          have recursive :=
            inductionHypothesis tailNonempty
          apply PegGrammar.Evaluates.nonterminal
          rw [grammar_rule_bits]
          change grammar.Evaluates
            (.orderedChoice
              (.sequence (.nonterminal bitName) (.nonterminal bitsName))
              (.nonterminal bitName))
            (LanguageCFG.bitTerminal bit ::
              LanguageCFG.bitWord (next :: rest) ++ remaining)
            (.success remaining)
          exact PegGrammar.Evaluates.choiceLeft
            (PegGrammar.Evaluates.sequenceSuccess opening recursive)

theorem entry_success_sound
    {input remaining : Word}
    (evaluation :
      grammar.Evaluates
        (.nonterminal entryName) input (.success remaining)) :
    EntryResidual input remaining := by
  cases evaluation with
  | nonterminal body =>
      rw [grammar_rule_entry] at body
      change grammar.Evaluates
        (.sequence (.terminal .langle)
          (.sequence (.nonterminal bitsName)
            (.sequence (.terminal .colon)
              (.sequence (.nonterminal bitsName)
                (.terminal .rangle)))))
        input (.success remaining) at body
      cases body with
      | sequenceSuccess openEvaluation afterOpen =>
          cases afterOpen with
          | sequenceSuccess keyEvaluation afterKey =>
              cases afterKey with
              | sequenceSuccess colonEvaluation afterColon =>
                  cases afterColon with
                  | sequenceSuccess payloadEvaluation closeEvaluation =>
                      have inputEquation := terminal_success openEvaluation
                      rcases bits_success_sound keyEvaluation with
                        ⟨key, keyNonempty, keyEquation⟩
                      have colonEquation := terminal_success colonEvaluation
                      rcases bits_success_sound payloadEvaluation with
                        ⟨payload, payloadNonempty, payloadEquation⟩
                      have closeEquation := terminal_success closeEvaluation
                      refine ⟨⟨key, payload⟩,
                        ⟨keyNonempty, payloadNonempty⟩, ?_⟩
                      rw [inputEquation, keyEquation, colonEquation,
                        payloadEquation, closeEquation]
                      simp [LanguageCFG.recordWord, List.append_assoc]

private def EntryBoundary (input : Word) : Prop :=
  ∀ remaining, input ≠ LanguageCFG.Terminal.langle :: remaining

private theorem entry_fails_at_boundary
    {input : Word} (boundary : EntryBoundary input) :
    grammar.Evaluates (.nonterminal entryName) input .failure := by
  apply PegGrammar.Evaluates.nonterminal
  rw [grammar_rule_entry]
  change grammar.Evaluates
    (.sequence (.terminal .langle)
      (.sequence (.nonterminal bitsName)
        (.sequence (.terminal .colon)
          (.sequence (.nonterminal bitsName)
            (.terminal .rangle)))))
    input .failure
  apply PegGrammar.Evaluates.sequenceFailure
  cases input with
  | nil =>
      exact evaluates_terminal_nil .langle
  | cons head remaining =>
      have different : head ≠ .langle := by
        intro equality
        subst head
        exact boundary remaining rfl
      exact evaluates_terminal_mismatch different remaining

theorem entry_complete
    (record : LanguageCFG.Record) (remaining : Word)
    (valid : record.Valid) :
    grammar.Evaluates
      (.nonterminal entryName)
      (LanguageCFG.recordWord record ++ remaining)
      (.success remaining) := by
  rcases valid with ⟨keyNonempty, payloadNonempty⟩
  have keyBoundary :
      BitBoundary
        (.colon :: (LanguageCFG.bitWord record.payload ++
          .rangle :: remaining)) := by
    intro bit tail equality
    cases bit <;> cases equality
  have payloadBoundary :
      BitBoundary (.rangle :: remaining) := by
    intro bit tail equality
    cases bit <;> cases equality
  have openEvaluation :=
    evaluates_terminal_match .langle
      (LanguageCFG.bitWord record.key ++
        .colon :: (LanguageCFG.bitWord record.payload ++
          .rangle :: remaining))
  have keyEvaluation :=
    bits_complete record.key
      (.colon :: (LanguageCFG.bitWord record.payload ++
        .rangle :: remaining))
      keyNonempty keyBoundary
  have colonEvaluation :=
    evaluates_terminal_match .colon
      (LanguageCFG.bitWord record.payload ++ .rangle :: remaining)
  have payloadEvaluation :=
    bits_complete record.payload (.rangle :: remaining)
      payloadNonempty payloadBoundary
  have closeEvaluation :=
    evaluates_terminal_match .rangle remaining
  apply PegGrammar.Evaluates.nonterminal
  rw [grammar_rule_entry]
  change grammar.Evaluates
    (.sequence (.terminal .langle)
      (.sequence (.nonterminal bitsName)
        (.sequence (.terminal .colon)
          (.sequence (.nonterminal bitsName)
            (.terminal .rangle)))))
    (LanguageCFG.recordWord record ++ remaining)
    (.success remaining)
  simpa [LanguageCFG.recordWord, List.append_assoc] using
    (PegGrammar.Evaluates.sequenceSuccess openEvaluation
      (PegGrammar.Evaluates.sequenceSuccess keyEvaluation
        (PegGrammar.Evaluates.sequenceSuccess colonEvaluation
          (PegGrammar.Evaluates.sequenceSuccess
            payloadEvaluation closeEvaluation))))

theorem rest_success_sound
    {input remaining : Word}
    (evaluation :
      grammar.Evaluates
        (.nonterminal restName) input (.success remaining)) :
    RestResidual input remaining := by
  cases evaluation with
  | nonterminal body =>
      rw [grammar_rule_rest] at body
      change grammar.Evaluates
        (.orderedChoice
          (.sequence (.nonterminal entryName) (.nonterminal restName))
          .empty)
        input (.success remaining) at body
      cases body with
      | choiceLeft recursive =>
          cases recursive with
          | sequenceSuccess first rest =>
              rcases entry_success_sound first with
                ⟨record, valid, inputEquation⟩
              rcases rest_success_sound rest with
                ⟨records, recordsValid, restEquation⟩
              refine ⟨record :: records, ?_, ?_⟩
              · intro current member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact valid
                · exact recordsValid current member
              · rw [inputEquation, restEquation,
                  LanguageCFG.recordsWord_cons]
                simp [List.append_assoc]
      | choiceRight _ emptyEvaluation =>
          cases emptyEvaluation
          exact ⟨[], by simp, by simp⟩
termination_by input.length
decreasing_by
  rw [inputEquation]
  simp [LanguageCFG.recordWord]
  omega

theorem rest_complete
    (records : List LanguageCFG.Record) (remaining : Word)
    (recordsValid : ∀ record ∈ records, record.Valid)
    (boundary : EntryBoundary remaining) :
    grammar.Evaluates
      (.nonterminal restName)
      (LanguageCFG.recordsWord records ++ remaining)
      (.success remaining) := by
  induction records with
  | nil =>
      have entryFailure := entry_fails_at_boundary boundary
      apply PegGrammar.Evaluates.nonterminal
      rw [grammar_rule_rest]
      change grammar.Evaluates
        (.orderedChoice
          (.sequence (.nonterminal entryName) (.nonterminal restName))
          .empty)
        remaining (.success remaining)
      exact .choiceRight
        (.sequenceFailure entryFailure)
        (.empty remaining)
  | cons record records inductionHypothesis =>
      have valid : record.Valid :=
        recordsValid record (by simp)
      have tailValid :
          ∀ current ∈ records, current.Valid := by
        intro current member
        exact recordsValid current (by simp [member])
      have firstEvaluation :=
        entry_complete record
          (LanguageCFG.recordsWord records ++ remaining) valid
      have restEvaluation :=
        inductionHypothesis tailValid
      apply PegGrammar.Evaluates.nonterminal
      rw [grammar_rule_rest]
      change grammar.Evaluates
        (.orderedChoice
          (.sequence (.nonterminal entryName) (.nonterminal restName))
          .empty)
        (LanguageCFG.recordsWord (record :: records) ++ remaining)
        (.success remaining)
      rw [LanguageCFG.recordsWord_cons, List.append_assoc]
      exact .choiceLeft
        (.sequenceSuccess firstEvaluation restEvaluation)

end Correctness

end PegSeparation.Witness.DirectPEG
