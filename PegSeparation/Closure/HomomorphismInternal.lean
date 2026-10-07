import PegSeparation.Closure.HomomorphismInternalMarkedProduct
import PegSeparation.Closure.WordHom
import PegSeparation.Closure.Assembly


namespace PegSeparation.Closure

open PegSeparation
open PegSeparation.Witness.LanguageCFG

namespace HomomorphismInternal

universe u v

variable {Source : Type u} {Target : Type v}

def wordHomImage
    (hom : WordHom Source Target)
    (language : Language Source) :
    Language Target := fun output =>
  ∃ input, input ∈ language ∧ hom.extend input = output

def ClosedUnderWordHomomorphism
    (sourceClass : Language Source → Prop)
    (targetClass : Language Target → Prop) : Prop :=
  ∀ (hom : WordHom Source Target) (language : Language Source),
    sourceClass language → targetClass (wordHomImage hom language)

abbrev Substitution (Source : Type u) (Target : Type v) :=
  Source → Language Target

inductive Substitutes
    (substitution : Substitution Source Target) :
    List Source → List Target → Prop where
  | nil : Substitutes substitution [] []
  | cons
      {symbol : Source}
      {input : List Source}
      {chunk output : List Target}
      (chunkMember : chunk ∈ substitution symbol)
      (tailSubstitutes : Substitutes substitution input output) :
      Substitutes substitution (symbol :: input) (chunk ++ output)

def substitutionImage
    (substitution : Substitution Source Target)
    (language : Language Source) :
    Language Target := fun output =>
  ∃ input, input ∈ language ∧ Substitutes substitution input output

def ClosedUnderSubstitution
    (sourceClass : Language Source → Prop)
    (componentClass targetClass : Language Target → Prop) : Prop :=
  ∀ (substitution : Substitution Source Target)
      (language : Language Source),
    sourceClass language →
      (∀ symbol, componentClass (substitution symbol)) →
        targetClass (substitutionImage substitution language)

def singletonSubstitution
    (hom : WordHom Source Target) :
    Substitution Source Target :=
  fun symbol output => output = hom.letterImage symbol

theorem substitutes_singleton_iff
    (hom : WordHom Source Target)
    (input : List Source)
    (output : List Target) :
    Substitutes (singletonSubstitution hom) input output ↔
      output = hom.extend input := by
  constructor
  · intro substituted
    induction substituted with
    | nil =>
        rfl
    | cons chunkMember tailSubstitutes ih =>
        change _ = hom.letterImage _ at chunkMember
        subst chunkMember
        simp [ih]
  · intro outputEq
    induction input generalizing output with
    | nil =>
        simp only [WordHom.extend_nil] at outputEq
        subst output
        exact .nil
    | cons symbol input ih =>
        rw [WordHom.extend_cons] at outputEq
        subst output
        exact .cons rfl (ih (hom.extend input) rfl)

theorem substitutionImage_singleton_eq_wordHomImage
    (hom : WordHom Source Target)
    (language : Language Source) :
    substitutionImage (singletonSubstitution hom) language =
      wordHomImage hom language := by
  ext output
  constructor
  · rintro ⟨input, inputMember, substituted⟩
    exact ⟨input, inputMember,
      (substitutes_singleton_iff hom input output).mp substituted |>.symm⟩
  · rintro ⟨input, inputMember, outputEq⟩
    exact ⟨input, inputMember,
      (substitutes_singleton_iff hom input output).mpr outputEq.symm⟩


section SingletonPEG

variable {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]

noncomputable def literalWordExpr
    (count : Nat) :
    List Alphabet → ParsingExpression Alphabet count
  | [] => endOfInput Alphabet count
  | symbol :: rest =>
      .sequence (.terminal symbol) (literalWordExpr count rest)

theorem literalWordExpr_total
    {count : Nat}
    (grammar : PegGrammar Alphabet count)
    (word input : List Alphabet) :
    ∃ result,
      grammar.Evaluates (literalWordExpr count word) input result := by
  induction word generalizing input with
  | nil =>
      cases input with
      | nil =>
          exact ⟨.success [],
            evaluates_endOfInput_nil grammar⟩
      | cons head tail =>
          exact ⟨.failure,
            evaluates_endOfInput_cons grammar head tail⟩
  | cons symbol rest ih =>
      apply PegGrammar.PartialTotalityHelpers.sequence_total
      · exact ⟨PegGrammar.terminalResult symbol input,
          .terminal symbol input⟩
      · intro middle
        exact ih middle

private theorem sequence_success_components
    {count : Nat}
    {grammar : PegGrammar Alphabet count}
    {left right : ParsingExpression Alphabet count}
    {input remaining : List Alphabet}
    (evaluation :
      grammar.Evaluates (.sequence left right) input (.success remaining)) :
    ∃ middle,
      grammar.Evaluates left input (.success middle) ∧
        grammar.Evaluates right middle (.success remaining) := by
  cases evaluation with
  | sequenceSuccess leftEvaluation rightEvaluation =>
      exact ⟨_, leftEvaluation, rightEvaluation⟩

private theorem terminal_success_iff
    {count : Nat}
    (grammar : PegGrammar Alphabet count)
    (wanted : Alphabet)
    (input remaining : List Alphabet) :
    grammar.Evaluates (.terminal wanted) input (.success remaining) ↔
      input = wanted :: remaining := by
  constructor
  · intro evaluation
    have canonical :
        grammar.Evaluates (.terminal wanted) input
          (PegGrammar.terminalResult wanted input) :=
      .terminal wanted input
    have same :=
      PegSeparation.External.LoffForwardRepaired.PegGrammar.evaluates_deterministic
        evaluation canonical
    cases input with
    | nil =>
        simp [PegGrammar.terminalResult] at same
    | cons actual tail =>
        by_cases equal : actual = wanted
        · subst actual
          simp [PegGrammar.terminalResult] at same
          cases same
          rfl
        · simp [PegGrammar.terminalResult, equal] at same
  · rintro rfl
    simpa [PegGrammar.terminalResult] using
      (PegGrammar.Evaluates.terminal (grammar := grammar) wanted
        (wanted :: remaining))

theorem literalWordExpr_success_iff
    {count : Nat}
    (grammar : PegGrammar Alphabet count)
    (word input : List Alphabet) :
    grammar.Evaluates (literalWordExpr count word) input (.success []) ↔
      input = word := by
  induction word generalizing input with
  | nil =>
      constructor
      · intro evaluation
        cases input with
        | nil =>
            rfl
        | cons head tail =>
            have failure :=
              evaluates_endOfInput_cons grammar head tail
            have impossible :=
              PegSeparation.External.LoffForwardRepaired.PegGrammar.evaluates_deterministic
                evaluation failure
            simp at impossible
      · rintro rfl
        exact evaluates_endOfInput_nil grammar
  | cons symbol rest ih =>
      constructor
      · intro evaluation
        obtain ⟨middle, symbolEvaluation, restEvaluation⟩ :=
          sequence_success_components evaluation
        have inputEq :
            input = symbol :: middle :=
          (terminal_success_iff grammar symbol input middle).mp
            symbolEvaluation
        rw [inputEq, (ih middle).mp restEvaluation]
      · rintro rfl
        exact .sequenceSuccess
          ((terminal_success_iff grammar symbol
            (symbol :: rest) rest).mpr rfl)
          ((ih rest).mpr rfl)

noncomputable def literalWordGrammar
    (word : List Alphabet) :
    PegGrammar Alphabet 1 where
  rule _ := literalWordExpr 1 word
  start := 0

theorem literalWordGrammar_isLoffTotal
    (word : List Alphabet) :
    (literalWordGrammar word).IsLoffTotal := by
  apply PegGrammar.PartialTotalityHelpers.loffTotal_of_nonterminal_total
  intro name input
  obtain ⟨result, evaluation⟩ :=
    literalWordExpr_total (literalWordGrammar word) word input
  exact ⟨result, .nonterminal (by
    simpa [literalWordGrammar] using evaluation)⟩

theorem literalWordGrammar_recognizes_iff
    (word input : List Alphabet) :
    (literalWordGrammar word).Recognizes input ↔ input = word := by
  constructor
  · intro recognized
    cases recognized with
    | nonterminal evaluation =>
        apply
          (literalWordExpr_success_iff
            (literalWordGrammar word) word input).mp
        simpa [literalWordGrammar] using evaluation
  · intro inputEq
    rw [inputEq, PegGrammar.Recognizes]
    exact .nonterminal (by
      simpa [literalWordGrammar] using
        (literalWordExpr_success_iff
          (literalWordGrammar word) word word).mpr rfl)

theorem recognizedByTotalPEG_singletonWord
    (word : List Alphabet) :
    RecognizedByTotalPEG
      (fun input : List Alphabet => input = word) :=
  ⟨1, literalWordGrammar word,
    literalWordGrammar_isLoffTotal word,
    literalWordGrammar_recognizes_iff word⟩

end SingletonPEG


def eraseSentinelHom {Alphabet : Type} :
    WordHom (Option Alphabet) Alphabet where
  letterImage
    | none => []
    | some symbol => [symbol]

@[simp] theorem eraseSentinelHom_none {Alphabet : Type} :
    (eraseSentinelHom (Alphabet := Alphabet)).letterImage none = [] :=
  rfl

@[simp] theorem eraseSentinelHom_some
    {Alphabet : Type} (symbol : Alphabet) :
    (eraseSentinelHom (Alphabet := Alphabet)).letterImage (some symbol) =
      [symbol] :=
  rfl

@[simp] theorem eraseSentinelHom_liftWord
    {Alphabet : Type} (word : List Alphabet) :
    (eraseSentinelHom (Alphabet := Alphabet)).extend (liftWord word) =
      word := by
  induction word with
  | nil =>
      rfl
  | cons symbol rest ih =>
      simp [ih]

@[simp] theorem eraseSentinelHom_marked
    {Alphabet : Type}
    (before after : List Alphabet) :
    (eraseSentinelHom (Alphabet := Alphabet)).extend
        (liftWord before ++ none :: liftWord after) =
      before ++ after := by
  simp

theorem wordHomImage_erase_markedProduct
    {Alphabet : Type}
    (left right : Language Alphabet) :
    wordHomImage (eraseSentinelHom (Alphabet := Alphabet))
        (MarkedProduct left right) =
      left * right := by
  ext output
  constructor
  · rintro ⟨marked, ⟨before, beforeMember, after, afterMember, markedEq⟩,
      outputEq⟩
    subst marked
    rw [eraseSentinelHom_marked] at outputEq
    exact Language.mem_mul.mpr
      ⟨before, beforeMember, after, afterMember, outputEq⟩
  · intro outputMember
    obtain ⟨before, beforeMember, after, afterMember, outputEq⟩ :=
      Language.mem_mul.mp outputMember
    refine
      ⟨liftWord before ++ none :: liftWord after,
        ⟨before, beforeMember, after, afterMember, rfl⟩, ?_⟩
    rw [eraseSentinelHom_marked, outputEq]


def MarkedConcatenationWitness :
    Language (Option Terminal) :=
  MarkedProduct Pref RegularTail

theorem markedConcatenationWitness_isPEG :
    RecognizedByTotalPEG MarkedConcatenationWitness := by
  exact recognizedByTotalPEG_markedProduct pref_isPEG regularTail_isPEG

theorem markedConcatenationWitness_erases :
    wordHomImage (eraseSentinelHom (Alphabet := Terminal))
        MarkedConcatenationWitness =
      Pref * RegularTail :=
  wordHomImage_erase_markedProduct Pref RegularTail

theorem homomorphism_nonclosure_internal
    (external : PegSeparation.ExternalAssumptions) :
    ∃ (language : Language (Option Terminal))
        (hom : WordHom (Option Terminal) Terminal),
      RecognizedByTotalPEG language ∧
        ¬ RecognizedByTotalPEG (wordHomImage hom language) := by
  refine ⟨MarkedConcatenationWitness,
    eraseSentinelHom, markedConcatenationWitness_isPEG, ?_⟩
  rw [markedConcatenationWitness_erases]
  exact (concatenation_nonclosure external).2.2

theorem totalPEG_not_closed_under_homomorphism_internal
    (external : PegSeparation.ExternalAssumptions) :
    ¬ ClosedUnderWordHomomorphism
        (fun language : Language (Option Terminal) =>
          RecognizedByTotalPEG language)
        (fun language : Language Terminal =>
          RecognizedByTotalPEG language) := by
  intro closed
  have imageRecognized :=
    closed (eraseSentinelHom (Alphabet := Terminal))
      MarkedConcatenationWitness markedConcatenationWitness_isPEG
  rw [markedConcatenationWitness_erases] at imageRecognized
  exact (concatenation_nonclosure external).2.2 imageRecognized

theorem eraseSingletonSubstitution_components_arePEG :
    ∀ symbol : Option Terminal,
      RecognizedByTotalPEG
        (singletonSubstitution
          (eraseSentinelHom (Alphabet := Terminal)) symbol) := by
  intro symbol
  exact recognizedByTotalPEG_singletonWord
    ((eraseSentinelHom (Alphabet := Terminal)).letterImage symbol)

theorem substitution_nonclosure_internal
    (external : PegSeparation.ExternalAssumptions) :
    ∃ (language : Language (Option Terminal))
        (substitution : Substitution (Option Terminal) Terminal),
      RecognizedByTotalPEG language ∧
        (∀ symbol, RecognizedByTotalPEG (substitution symbol)) ∧
          ¬ RecognizedByTotalPEG
            (substitutionImage substitution language) := by
  refine ⟨MarkedConcatenationWitness,
    singletonSubstitution (eraseSentinelHom (Alphabet := Terminal)),
    markedConcatenationWitness_isPEG,
    eraseSingletonSubstitution_components_arePEG, ?_⟩
  rw [substitutionImage_singleton_eq_wordHomImage,
    markedConcatenationWitness_erases]
  exact (concatenation_nonclosure external).2.2

theorem totalPEG_not_closed_under_substitution_internal
    (external : PegSeparation.ExternalAssumptions) :
    ¬ ClosedUnderSubstitution
        (fun language : Language (Option Terminal) =>
          RecognizedByTotalPEG language)
        (fun language : Language Terminal =>
          RecognizedByTotalPEG language)
        (fun language : Language Terminal =>
          RecognizedByTotalPEG language) := by
  intro closed
  have imageRecognized :=
    closed
      (singletonSubstitution
        (eraseSentinelHom (Alphabet := Terminal)))
      MarkedConcatenationWitness
      markedConcatenationWitness_isPEG
      eraseSingletonSubstitution_components_arePEG
  rw [substitutionImage_singleton_eq_wordHomImage,
    markedConcatenationWitness_erases] at imageRecognized
  exact (concatenation_nonclosure external).2.2 imageRecognized

end HomomorphismInternal

end PegSeparation.Closure
