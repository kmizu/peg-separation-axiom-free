import PegSeparation.CFLNotPEG.External.LarsenYuBetaOneRepaired
import PegSeparation.CFLNotPEG.External.LarsenYuCostMonotonicity
import PegSeparation.CFLNotPEG.External.LarsenYuExperimentAdvantage
import PegSeparation.CFLNotPEG.External.LarsenYuLargeAssembly
import PegSeparation.CFLNotPEG.External.LarsenYuNoopNormalization
import PegSeparation.CFLNotPEG.External.LarsenYuQuantitativeSelector


open scoped BigOperators

namespace PegSeparation.External.LarsenYuBetaOneInternal

noncomputable section

open LarsenYuBaseView LarsenYuBetaOneRepaired LarsenYuCostMonotonicity
  LarsenYuExperimentAdvantage LarsenYuExperimentPosterior
  LarsenYuLargeAssembly LarsenYuNoopNormalization LarsenYuPairOverflow
  LarsenYuPeakQuantitative LarsenYuPosteriorFiltering
  LarsenYuQuantitativeSelector PeakToAverage
  LarsenYuBaseView.CellProbe.StaticStructure
  LarsenYuExperimentAdvantage.CellProbe.StaticStructure
  LarsenYuExperimentPosterior.CellProbe.StaticStructure
  LarsenYuLargeAssembly.CellProbe.StaticStructure
  LarsenYuPairOverflow.CellProbe.StaticStructure
  LarsenYuQuantitativeSelector.CellProbe.StaticStructure

namespace CellProbe.StaticStructure

variable {Input Query : Type} [Fintype Input] [Fintype Query]
  {wordBits cacheCells maxUpdatedCells : Nat}

local instance samplingViewDecidableEq :
    DecidableEq (SamplingView Query wordBits cacheCells) :=
  Classical.decEq _

theorem exists_protocol_largeRegime_strict
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (p : ℝ)
    (hword : 0 < wordBits)
    (_hbalanced : problem.IsBalanced inputDistribution)
    (hsolves : dataStructure.Solves problem)
    (hp : 0 < p) (hhalf : p ≤ (1 / 2 : ℝ))
    (hlarge : 4 ≤ p * (maxUpdatedCells : ℝ)) :
    ∃ (messageBits coinCount : Nat)
      (protocol : PublicCoinProtocol Input messageBits coinCount),
      (messageBits : ℝ) <
          (8 * p * (maxUpdatedCells : ℝ) + (cacheCells : ℝ)) *
              (wordBits : ℝ) + 2 ∧
        Real.rpow 2
            (-512 *
              (Real.sqrt
                (dataStructure.expectedTotalProbes
                    inputDistribution queryDistribution *
                  (1 + dataStructure.expectedUpdatedProbes
                    inputDistribution queryDistribution * log₂ (1 / p))) +
                (1 + dataStructure.expectedUpdatedProbes
                  inputDistribution queryDistribution * log₂ (1 / p))) *
              log₂ (1 / p)) -
            Real.rpow 2 (-(1 / 4 : ℝ) * p * maxUpdatedCells) ≤
          protocol.advantage problem inputDistribution queryDistribution := by
  let normalized := eraseNoopUpdates dataStructure
  have hsolvesNormalized : normalized.Solves problem := by
    simpa only [normalized] using
      solves_eraseNoopUpdates dataStructure problem hsolves
  have heffective : ∀ input address,
      address ∈ normalized.updatedAddresses input →
        normalized.updatedWord input address ≠
          normalized.preMemory address := by
    intro input address hmem
    simpa only [normalized] using
      mem_updatedAddresses_implies_effective dataStructure input address hmem
  obtain ⟨selector, hselectorCard, hselectorFiber⟩ :=
    exists_quantitativeCoordinateSelector normalized problem hsolvesNormalized
      inputDistribution queryDistribution p hp hhalf
  let degree := samplingRevealBudget
    (normalized.expectedTotalProbes inputDistribution queryDistribution)
    (normalized.expectedUpdatedProbes inputDistribution queryDistribution) p
  have hdegree : ∀ selectedView,
      (selector selectedView).card ≤ degree := by
    intro selectedView
    simpa [degree, coordinateBudget, samplingRevealBudget, samplingShape] using
      hselectorCard selectedView
  have hreveal :
      p ^ degree *
        (∑ selectedView : SamplingView Query wordBits cacheCells,
          coarseMass
              (samplingExperimentDistribution (wordBits := wordBits)
                inputDistribution queryDistribution p hp.le
                  (hhalf.trans (by norm_num)))
              (samplingView normalized) selectedView *
            fiberL1
              (experimentPosterior normalized problem inputDistribution
                queryDistribution p hp.le
                  (hhalf.trans (by norm_num)) selectedView)
              (selector selectedView)) ≤
        LarsenYuCoinTransport.outcomeStructuredAdvantage
          (pairMaskDistribution (wordBits := wordBits) p hp.le
            (hhalf.trans (by norm_num)))
          (experimentEncode normalized) problem inputDistribution
            queryDistribution := by
    have hraw :=
      pow_degree_mul_selectedFiberSum_le_outcomeStructuredAdvantage
        normalized problem inputDistribution queryDistribution p hp.le
          (hhalf.trans (by norm_num)) degree selector hdegree
    simpa [experimentPosterior, pairMaskDistribution] using hraw
  have hrevealBudget :
      p ^ samplingRevealBudget
          (normalized.expectedTotalProbes inputDistribution queryDistribution)
          (normalized.expectedUpdatedProbes inputDistribution
            queryDistribution) p *
        (∑ selectedView : SamplingView Query wordBits cacheCells,
          coarseMass
              (samplingExperimentDistribution (wordBits := wordBits)
                inputDistribution queryDistribution p hp.le
                  (hhalf.trans (by norm_num)))
              (samplingView normalized) selectedView *
            fiberL1
              (experimentPosterior normalized problem inputDistribution
                queryDistribution p hp.le
                  (hhalf.trans (by norm_num)) selectedView)
              (selector selectedView)) ≤
        LarsenYuCoinTransport.outcomeStructuredAdvantage
          (pairMaskDistribution (wordBits := wordBits) p hp.le
            (hhalf.trans (by norm_num)))
          (experimentEncode normalized) problem inputDistribution
            queryDistribution := by
    simpa only [degree] using hreveal
  obtain ⟨messageBits, coinCount, protocol, hmessage, hadvantageNormalized⟩ :=
    exists_protocol_strict_of_reveal normalized heffective problem
      inputDistribution queryDistribution p hp hhalf hword hlarge selector
        hselectorFiber hrevealBudget
  have htotal :
      normalized.expectedTotalProbes inputDistribution queryDistribution ≤
        dataStructure.expectedTotalProbes inputDistribution
          queryDistribution := by
    simpa only [normalized] using
      (expectedTotalProbes_eraseNoopUpdates dataStructure inputDistribution
        queryDistribution).le
  have hupdated :
      normalized.expectedUpdatedProbes inputDistribution queryDistribution ≤
        dataStructure.expectedUpdatedProbes inputDistribution
          queryDistribution := by
    simpa only [normalized] using
      expectedUpdatedProbes_eraseNoopUpdates_le dataStructure
        inputDistribution queryDistribution
  have hmainMonotone :
      Real.rpow 2
          (-512 *
            (Real.sqrt
                (dataStructure.expectedTotalProbes
                    inputDistribution queryDistribution *
                  (1 + dataStructure.expectedUpdatedProbes
                    inputDistribution queryDistribution * log₂ (1 / p))) +
              (1 + dataStructure.expectedUpdatedProbes
                inputDistribution queryDistribution * log₂ (1 / p))) *
            log₂ (1 / p)) ≤
        Real.rpow 2
          (-512 *
            (Real.sqrt
                (normalized.expectedTotalProbes
                    inputDistribution queryDistribution *
                  (1 + normalized.expectedUpdatedProbes
                    inputDistribution queryDistribution * log₂ (1 / p))) +
              (1 + normalized.expectedUpdatedProbes
                inputDistribution queryDistribution * log₂ (1 / p))) *
            log₂ (1 / p)) := by
    exact mainTerm_mono_of_cost_le
      (A := (512 : ℝ))
      (actualTotal := normalized.expectedTotalProbes
        inputDistribution queryDistribution)
      (boundedTotal := dataStructure.expectedTotalProbes
        inputDistribution queryDistribution)
      (actualUpdated := normalized.expectedUpdatedProbes
        inputDistribution queryDistribution)
      (boundedUpdated := dataStructure.expectedUpdatedProbes
        inputDistribution queryDistribution)
      (p := p)
      (by norm_num)
      (normalized.expectedTotalProbes_nonneg inputDistribution
        queryDistribution)
      (normalized.expectedUpdatedProbes_nonneg inputDistribution
        queryDistribution)
      htotal hupdated hp hhalf
  refine ⟨messageBits, coinCount, protocol, hmessage, ?_⟩
  calc
    Real.rpow 2
          (-512 *
            (Real.sqrt
                (dataStructure.expectedTotalProbes
                    inputDistribution queryDistribution *
                  (1 + dataStructure.expectedUpdatedProbes
                    inputDistribution queryDistribution * log₂ (1 / p))) +
              (1 + dataStructure.expectedUpdatedProbes
                inputDistribution queryDistribution * log₂ (1 / p))) *
            log₂ (1 / p)) -
        Real.rpow 2 (-(1 / 4 : ℝ) * p * maxUpdatedCells) ≤
      Real.rpow 2
          (-512 *
            (Real.sqrt
                (normalized.expectedTotalProbes
                    inputDistribution queryDistribution *
                  (1 + normalized.expectedUpdatedProbes
                    inputDistribution queryDistribution * log₂ (1 / p))) +
              (1 + normalized.expectedUpdatedProbes
                inputDistribution queryDistribution * log₂ (1 / p))) *
            log₂ (1 / p)) -
        Real.rpow 2 (-(1 / 4 : ℝ) * p * maxUpdatedCells) :=
      sub_le_sub_right hmainMonotone _
    _ ≤ protocol.advantage problem inputDistribution queryDistribution :=
      hadvantageNormalized

end CellProbe.StaticStructure

theorem larsenYuLargeRegime_512_quarter :
    LarsenYuLargeRegimeAt (512 : ℝ) (1 / 4 : ℝ) := by
  intro Input Query instInput instQuery wordBits cacheCells maxUpdatedCells
    problem inputDistribution queryDistribution dataStructure p hword hbalanced
    hsolves hp hhalf hlarge
  exact CellProbe.StaticStructure.exists_protocol_largeRegime_strict
    problem inputDistribution queryDistribution dataStructure p hword hbalanced
      hsolves hp hhalf hlarge

theorem larsenYuBetaOneInternal : LarsenYuBetaOneExactStatement := by
  exact larsenYuBetaOneExact_of_largeRegime
    (A := (512 : ℝ)) (a := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    larsenYuLargeRegime_512_quarter

end

end PegSeparation.External.LarsenYuBetaOneInternal
