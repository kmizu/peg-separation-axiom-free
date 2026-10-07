import PegSeparation.CFLNotPEG.External.LarsenYuCappedOutcome
import PegSeparation.CFLNotPEG.External.LarsenYuCoinTransport
import PegSeparation.CFLNotPEG.External.LarsenYuMainTerm
import PegSeparation.CFLNotPEG.External.LarsenYuStrictMessageBound


open scoped BigOperators

namespace PegSeparation.External.LarsenYuLargeAssembly

noncomputable section

open LarsenYuBaseView LarsenYuBernoulli LarsenYuCappedCodec
  LarsenYuCappedOutcome LarsenYuCoinTransport LarsenYuExperimentAdvantage
  LarsenYuExperimentPosterior LarsenYuMainTerm LarsenYuMessageCodecBounds
  LarsenYuPairOverflow LarsenYuPeakQuantitative LarsenYuPosteriorFiltering
  LarsenYuQuantitativeSelector LarsenYuStrictMessageBound PeakToAverage
  LarsenYuBaseView.CellProbe.StaticStructure
  LarsenYuCappedCodec.CellProbe.StaticStructure
  LarsenYuCappedOutcome.CellProbe.StaticStructure
  LarsenYuExperimentAdvantage.CellProbe.StaticStructure
  LarsenYuExperimentPosterior.CellProbe.StaticStructure
  LarsenYuMainTerm.CellProbe.StaticStructure
  LarsenYuPairOverflow.CellProbe.StaticStructure
  LarsenYuQuantitativeSelector.CellProbe.StaticStructure

namespace CellProbe.StaticStructure

variable {Input Query : Type} [Fintype Input] [Fintype Query]
  {wordBits cacheCells maxUpdatedCells : Nat}

local instance samplingViewDecidableEq :
    DecidableEq (SamplingView Query wordBits cacheCells) :=
  Classical.decEq _

theorem exists_protocol_strict_of_reveal
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (heffective : ∀ input address,
      address ∈ dataStructure.updatedAddresses input →
        dataStructure.updatedWord input address ≠
          dataStructure.preMemory address)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 < p) (hhalf : p ≤ 1 / 2)
    (hword : 0 < wordBits)
    (hlarge : 4 ≤ p * (maxUpdatedCells : ℝ))
    (selector : (selectedView : SamplingView Query wordBits cacheCells) →
      Finset (Fin (simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card))
    (hselector : ∀ selectedView,
      QuantitativeGoodView dataStructure inputDistribution queryDistribution
        p hp.le (hhalf.trans (by norm_num)) selectedView →
      fiberReward dataStructure inputDistribution queryDistribution p ≤
        fiberL1
          (experimentPosterior dataStructure problem inputDistribution
            queryDistribution p hp.le (hhalf.trans (by norm_num)) selectedView)
          (selector selectedView))
    (hreveal :
      p ^ samplingRevealBudget
          (dataStructure.expectedTotalProbes
            inputDistribution queryDistribution)
          (dataStructure.expectedUpdatedProbes
            inputDistribution queryDistribution) p *
        (∑ selectedView : SamplingView Query wordBits cacheCells,
          coarseMass
              (samplingExperimentDistribution (wordBits := wordBits)
                inputDistribution queryDistribution p hp.le
                  (hhalf.trans (by norm_num)))
              (samplingView dataStructure) selectedView *
            fiberL1
              (experimentPosterior dataStructure problem inputDistribution
                queryDistribution p hp.le
                  (hhalf.trans (by norm_num)) selectedView)
              (selector selectedView)) ≤
        outcomeStructuredAdvantage
          (pairMaskDistribution (wordBits := wordBits) p hp.le
            (hhalf.trans (by norm_num)))
          (experimentEncode dataStructure) problem inputDistribution
            queryDistribution) :
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
  let coinDistribution :=
    pairMaskDistribution (wordBits := wordBits) p hp.le
      (hhalf.trans (by norm_num))
  let untruncatedAdvantage :=
    outcomeStructuredAdvantage coinDistribution
      (experimentEncode dataStructure) problem inputDistribution
        queryDistribution
  let cappedAdvantage :=
    outcomeStructuredAdvantage coinDistribution
      (cappedEncode dataStructure p) problem inputDistribution
        queryDistribution
  have hmain :
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
        untruncatedAdvantage := by
    have hraw := mainTerm_le_of_reveal_mul_selectedFiberSum_le
      dataStructure problem inputDistribution queryDistribution p hp hhalf
      selector hselector untruncatedAdvantage
    have hreveal' :
        p ^ samplingRevealBudget
            (dataStructure.expectedTotalProbes
              inputDistribution queryDistribution)
            (dataStructure.expectedUpdatedProbes
              inputDistribution queryDistribution) p *
          (∑ selectedView : SamplingView Query wordBits cacheCells,
            coarseMass
                (samplingExperimentDistribution (wordBits := wordBits)
                  inputDistribution queryDistribution p hp.le
                    (hhalf.trans (by norm_num)))
                (samplingView dataStructure) selectedView *
              fiberL1
                (experimentPosterior dataStructure problem inputDistribution
                  queryDistribution p hp.le
                    (hhalf.trans (by norm_num)) selectedView)
                (selector selectedView)) ≤
          untruncatedAdvantage := by
      simpa [untruncatedAdvantage, coinDistribution] using hreveal
    simpa [samplingLambda, samplingLogFactor] using hraw hreveal'
  have hcapped :
      untruncatedAdvantage -
          Real.rpow 2 (-(1 / 4 : ℝ) * p * maxUpdatedCells) ≤
        cappedAdvantage := by
    have hraw :=
      outcomeStructuredAdvantage_sub_quarter_rpow_le_cappedEncode
        dataStructure heffective problem inputDistribution queryDistribution p
          hp.le (hhalf.trans (by norm_num)) hlarge
    simpa [untruncatedAdvantage, cappedAdvantage, coinDistribution] using hraw
  let messageBits :=
    fixedMessageBits p maxUpdatedCells cacheCells wordBits
  obtain ⟨protocol, hprotocol⟩ :=
    exists_protocol_of_outcomeCoin_structured_card_le
      (messageBits := messageBits) coinDistribution
      (cappedEncode dataStructure p)
      (card_fixedPayload_le_fixedMessageBits p maxUpdatedCells cacheCells
        wordBits)
      problem inputDistribution queryDistribution
  refine ⟨messageBits, Fintype.card
      (Mask (CellProbe.Address wordBits) ×
        Mask (CellProbe.Address wordBits)), protocol, ?_, ?_⟩
  · dsimp only [messageBits]
    exact fixedMessageBits_lt hword hlarge
  · have hcombined :
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
          cappedAdvantage := by
      linarith
    exact hcombined.trans (by
      simpa [cappedAdvantage] using hprotocol)

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuLargeAssembly
