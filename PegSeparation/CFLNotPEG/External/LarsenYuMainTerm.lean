import PegSeparation.CFLNotPEG.External.LarsenYuSelectedReward
import PegSeparation.CFLNotPEG.External.LarsenYuPeakQuantitative


open scoped BigOperators

namespace PegSeparation.External.LarsenYuMainTerm

noncomputable section

open LarsenYuPosteriorFiltering LarsenYuExperimentPosterior
  LarsenYuExperimentPeak LarsenYuBaseView LarsenYuPeakQuantitative
  LarsenYuQuantitativeSelector LarsenYuSelectedReward PeakToAverage
  LarsenYuExperimentPosterior.CellProbe.StaticStructure
  LarsenYuExperimentPeak.CellProbe.StaticStructure
  LarsenYuBaseView.CellProbe.StaticStructure
  LarsenYuQuantitativeSelector.CellProbe.StaticStructure
  LarsenYuSelectedReward.CellProbe.StaticStructure



namespace CellProbe.StaticStructure

variable {Input Query : Type} [Fintype Input] [Fintype Query]
  {wordBits cacheCells maxUpdatedCells : Nat}

local instance samplingViewDecidableEq :
    DecidableEq (SamplingView Query wordBits cacheCells) :=
  Classical.decEq _


theorem mainTerm_le_of_reveal_mul_selectedFiberSum_le
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 < p) (hhalf : p ≤ 1 / 2)
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
    (untruncatedAdvantage : ℝ)
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
        untruncatedAdvantage) :
    Real.rpow 2
        (-512 *
          (Real.sqrt
              (dataStructure.expectedTotalProbes
                  inputDistribution queryDistribution *
                samplingLambda
                  (dataStructure.expectedUpdatedProbes
                    inputDistribution queryDistribution) p) +
            samplingLambda
              (dataStructure.expectedUpdatedProbes
                inputDistribution queryDistribution) p) *
          samplingLogFactor p) ≤
      untruncatedAdvantage := by
  let total := dataStructure.expectedTotalProbes
    inputDistribution queryDistribution
  let updated := dataStructure.expectedUpdatedProbes
    inputDistribution queryDistribution
  let degree := samplingRevealBudget total updated p
  let baseline := samplingPeakBaseline updated p
  let reward := fiberReward dataStructure inputDistribution queryDistribution p
  let selectedSum :=
    ∑ selectedView : SamplingView Query wordBits cacheCells,
      coarseMass
          (samplingExperimentDistribution (wordBits := wordBits)
            inputDistribution queryDistribution p hp.le
              (hhalf.trans (by norm_num)))
          (samplingView dataStructure) selectedView *
        fiberL1
          (experimentPosterior dataStructure problem inputDistribution
            queryDistribution p hp.le (hhalf.trans (by norm_num)) selectedView)
          (selector selectedView)
  have htotal : 0 ≤ total := by
    dsimp [total]
    exact dataStructure.expectedTotalProbes_nonneg
      inputDistribution queryDistribution
  have hupdated : 0 ≤ updated := by
    dsimp [updated]
    exact dataStructure.expectedUpdatedProbes_nonneg
      inputDistribution queryDistribution
  have habsorb :=
    two_rpow_neg_512_samplingShape_le_reveal_mul_peak_mul_fiberReward
      htotal hupdated hp hhalf
  have hselected : baseline * reward ≤ selectedSum := by
    dsimp [baseline, reward, selectedSum]
    exact peakBaseline_mul_fiberReward_le_selectedFiberSum
      dataStructure problem inputDistribution queryDistribution p hp hhalf
      selector hselector
  have hpowNonnegative : 0 ≤ p ^ degree := pow_nonneg hp.le degree
  calc
    Real.rpow 2
        (-512 *
          (Real.sqrt
              (dataStructure.expectedTotalProbes
                  inputDistribution queryDistribution *
                samplingLambda
                  (dataStructure.expectedUpdatedProbes
                    inputDistribution queryDistribution) p) +
            samplingLambda
              (dataStructure.expectedUpdatedProbes
                inputDistribution queryDistribution) p) *
          samplingLogFactor p) =
        Real.rpow 2
          (-512 * samplingShape total updated p * samplingLogFactor p) := by
      rfl
    _ ≤ p ^ degree * (baseline * reward) := by
      simpa [degree, baseline, reward, fiberReward, samplingShape, total,
        updated] using habsorb
    _ ≤ p ^ degree * selectedSum :=
      mul_le_mul_of_nonneg_left hselected hpowNonnegative
    _ ≤ untruncatedAdvantage := by
      simpa [degree, selectedSum, total, updated] using hreveal

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuMainTerm
