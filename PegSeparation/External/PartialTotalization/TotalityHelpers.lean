import PegSeparation.Common.Loff.Semantics


namespace PegSeparation.PegGrammar.PartialTotalityHelpers

open PegSeparation

variable {Terminal : Type} [DecidableEq Terminal]
  {nonterminalCount : Nat}
  {grammar : PegGrammar Terminal nonterminalCount}

theorem sequence_total
    {left right : ParsingExpression Terminal nonterminalCount}
    {input : List Terminal}
    (leftTotal : ∃ result, grammar.Evaluates left input result)
    (rightTotal : ∀ middle, ∃ result, grammar.Evaluates right middle result) :
    ∃ result, grammar.Evaluates (.sequence left right) input result := by
  rcases leftTotal with ⟨leftResult, leftEvaluation⟩
  cases leftResult with
  | failure =>
      exact ⟨.failure, .sequenceFailure leftEvaluation⟩
  | success middle =>
      rcases rightTotal middle with ⟨rightResult, rightEvaluation⟩
      exact ⟨rightResult, .sequenceSuccess leftEvaluation rightEvaluation⟩

theorem orderedChoice_total
    {left right : ParsingExpression Terminal nonterminalCount}
    {input : List Terminal}
    (leftTotal : ∃ result, grammar.Evaluates left input result)
    (rightTotal : ∃ result, grammar.Evaluates right input result) :
    ∃ result, grammar.Evaluates (.orderedChoice left right) input result := by
  rcases leftTotal with ⟨leftResult, leftEvaluation⟩
  cases leftResult with
  | failure =>
      rcases rightTotal with ⟨rightResult, rightEvaluation⟩
      exact ⟨rightResult, .choiceRight leftEvaluation rightEvaluation⟩
  | success remaining =>
      exact ⟨.success remaining, .choiceLeft leftEvaluation⟩

theorem notPredicate_total
    {body : ParsingExpression Terminal nonterminalCount}
    {input : List Terminal}
    (bodyTotal : ∃ result, grammar.Evaluates body input result) :
    ∃ result, grammar.Evaluates (.notPredicate body) input result := by
  rcases bodyTotal with ⟨bodyResult, bodyEvaluation⟩
  cases bodyResult with
  | failure =>
      exact ⟨.success input, .notSuccess bodyEvaluation⟩
  | success remaining =>
      exact ⟨.failure, .notFailure bodyEvaluation⟩

theorem andPredicate_total
    {body : ParsingExpression Terminal nonterminalCount}
    {input : List Terminal}
    (bodyTotal : ∃ result, grammar.Evaluates body input result) :
    ∃ result, grammar.Evaluates (.andPredicate body) input result := by
  rcases bodyTotal with ⟨bodyResult, bodyEvaluation⟩
  cases bodyResult with
  | failure =>
      exact ⟨.failure, .andFailure bodyEvaluation⟩
  | success remaining =>
      exact ⟨.success input, .andSuccess bodyEvaluation⟩

theorem loffTotal_of_nonterminal_total
    (nonterminalTotal :
      ∀ (name : Fin nonterminalCount) (input : List Terminal),
        ∃ result, grammar.Evaluates (.nonterminal name) input result) :
    grammar.IsLoffTotal := by
  intro expression input
  induction expression generalizing input with
  | empty =>
      exact ⟨.success input, .empty input⟩
  | failure =>
      exact ⟨.failure, .failure input⟩
  | terminal symbol =>
      exact ⟨terminalResult symbol input, .terminal symbol input⟩
  | nonterminal name =>
      exact nonterminalTotal name input
  | sequence left right leftTotal rightTotal =>
      exact sequence_total (leftTotal input) (fun middle => rightTotal middle)
  | orderedChoice left right leftTotal rightTotal =>
      exact orderedChoice_total (leftTotal input) (rightTotal input)
  | notPredicate body bodyTotal =>
      exact notPredicate_total (bodyTotal input)
  | andPredicate body bodyTotal =>
      exact andPredicate_total (bodyTotal input)

end PegSeparation.PegGrammar.PartialTotalityHelpers
