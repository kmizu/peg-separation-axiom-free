import PegSeparation.Common.Model.PEG
import PegSeparation.Common.Model.Scaffolding
import PegSeparation.CFLNotPEG.Model.Communication
import PegSeparation.CFLNotPEG.Reduction.MultiphaseModel


namespace PegSeparation

abbrev LoffForwardStatement : Prop :=
  ∀ {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    {nonterminalCount : Nat} (grammar : PegGrammar Terminal nonterminalCount),
    grammar.IsLoffTotal →
      ∃ (stateCount workLabelCount degree radius : Nat)
        (automaton : Scaffolding.Automaton Terminal
          stateCount workLabelCount degree radius),
        ∀ input,
          automaton.Accepts input ↔ grammar.Recognizes input.reverse

abbrev Ko2026MultiphaseIPLowerBoundStatement : Prop :=
  ¬ PegSeparation.Reduction.MultiphaseModel.HasFastMultiphaseIPFamily

abbrev LarsenYuBetaOneExactStatement : Prop :=
  ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
    ∀ {Input Query : Type} [Fintype Input] [Fintype Query]
      {wordBits cacheCells maxUpdatedCells : Nat}
      (problem : BinaryProblem Input Query)
      (inputDistribution : FiniteDistribution Input)
      (queryDistribution : FiniteDistribution Query)
      (dataStructure : CellProbe.StaticStructure Input Query
        wordBits cacheCells maxUpdatedCells)
      (p : ℝ),
      0 < wordBits →
      problem.IsBalanced inputDistribution →
      dataStructure.Solves problem →
      0 < p → p ≤ (1 / 2 : ℝ) →
      ∃ (messageBits coinCount : Nat)
        (protocol : PublicCoinProtocol Input messageBits coinCount),
        (messageBits : ℝ) <
            (8 * p * (maxUpdatedCells : ℝ) + (cacheCells : ℝ)) * (wordBits : ℝ) + 2 ∧
          Real.rpow 2
              (-A *
                (Real.sqrt
                  (dataStructure.expectedTotalProbes inputDistribution queryDistribution *
                    (1 + dataStructure.expectedUpdatedProbes
                      inputDistribution queryDistribution * log₂ (1 / p))) +
                  (1 + dataStructure.expectedUpdatedProbes
                    inputDistribution queryDistribution * log₂ (1 / p))) *
                log₂ (1 / p)) -
              Real.rpow 2 (-a * p * (maxUpdatedCells : ℝ)) ≤
            protocol.advantage problem inputDistribution queryDistribution

structure ExternalAssumptions : Type 1 where
  loffForward : LoffForwardStatement
  ko2026MultiphaseIPLowerBound : Ko2026MultiphaseIPLowerBoundStatement

structure InternalLowerBoundAssumptions : Type 1 where
  larsenYuBetaOne : LarsenYuBetaOneExactStatement

end PegSeparation
