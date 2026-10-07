import PegSeparation.CFLNotPEG.External.LarsenYuQuantitativeSelector


open scoped BigOperators

namespace PegSeparation.External.LarsenYuSelectedReward

noncomputable section

open LarsenYuPosteriorFiltering LarsenYuExperimentPosterior
  LarsenYuExperimentPeak LarsenYuBaseView LarsenYuPeakQuantitative
  LarsenYuQuantitativeSelector LarsenYuCoordinateSelector PeakToAverage
  LarsenYuExperimentPosterior.CellProbe.StaticStructure
  LarsenYuExperimentPeak.CellProbe.StaticStructure
  LarsenYuBaseView.CellProbe.StaticStructure
  LarsenYuQuantitativeSelector.CellProbe.StaticStructure

namespace CellProbe.StaticStructure

variable {Input Query : Type} [Fintype Input] [Fintype Query]
  {wordBits cacheCells maxUpdatedCells : Nat}

local instance samplingViewDecidableEq :
    DecidableEq (SamplingView Query wordBits cacheCells) :=
  Classical.decEq _

local instance samplingSuccessDecidable
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    DecidablePred
      (samplingSuccess dataStructure inputDistribution queryDistribution) :=
  fun _ ↦ Classical.propDecidable _

local instance quantitativeGoodViewDecidable
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1) :
    DecidablePred (QuantitativeGoodView dataStructure inputDistribution
      queryDistribution p hp hpone) :=
  fun _ ↦ Classical.propDecidable _

theorem samplingPeakBaseline_le_quantitativeGoodViewMass
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    let distribution := samplingExperimentDistribution (wordBits := wordBits)
      inputDistribution queryDistribution p hp.le (hhalf.trans (by norm_num))
    let updated := dataStructure.expectedUpdatedProbes
      inputDistribution queryDistribution
    samplingPeakBaseline updated p ≤
      ∑ selectedView : SamplingView Query wordBits cacheCells,
        if QuantitativeGoodView dataStructure inputDistribution
          queryDistribution p hp.le (hhalf.trans (by norm_num)) selectedView
        then coarseMass distribution (samplingView dataStructure) selectedView
        else 0 := by
  classical
  dsimp only
  let hpone : p ≤ (1 : ℝ) := hhalf.trans (by norm_num)
  let distribution := samplingExperimentDistribution (wordBits := wordBits)
    inputDistribution queryDistribution p hp.le hpone
  let updated := dataStructure.expectedUpdatedProbes
    inputDistribution queryDistribution
  let baseline := samplingPeakBaseline updated p
  have hfiltered := half_globalBaseline_le_goodSamplingViewMass
    dataStructure inputDistribution queryDistribution p hp hpone
  have hbaselineEq :
      ((1 / 2 : ℝ) * Real.rpow p (4 * updated)) / 2 = baseline := by
    dsimp [baseline, samplingPeakBaseline]
    ring
  have hthreshold : baseline ≤
      ∑ selectedView : SamplingView Query wordBits cacheCells,
        if baseline *
            coarseMass distribution (samplingView dataStructure) selectedView ≤
          successMass distribution (samplingView dataStructure)
            (samplingSuccess dataStructure inputDistribution queryDistribution)
            selectedView
        then coarseMass distribution (samplingView dataStructure) selectedView
        else 0 := by
    dsimp only at hfiltered
    have hrewrite :
        ((1 / 2 : ℝ) * Real.rpow p
          (4 * dataStructure.expectedUpdatedProbes
            inputDistribution queryDistribution)) / 2 = baseline := by
      simpa [updated] using hbaselineEq
    rw [hrewrite] at hfiltered
    simpa [distribution, updated, hpone] using hfiltered
  calc
    baseline ≤ ∑ selectedView : SamplingView Query wordBits cacheCells,
        if baseline *
            coarseMass distribution (samplingView dataStructure) selectedView ≤
          successMass distribution (samplingView dataStructure)
            (samplingSuccess dataStructure inputDistribution queryDistribution)
            selectedView
        then coarseMass distribution (samplingView dataStructure) selectedView
        else 0 := hthreshold
    _ = ∑ selectedView : SamplingView Query wordBits cacheCells,
        if QuantitativeGoodView dataStructure inputDistribution
          queryDistribution p hp.le hpone selectedView
        then coarseMass distribution (samplingView dataStructure) selectedView
        else 0 := by
      apply Finset.sum_congr rfl
      intro selectedView _hselectedView
      let mass := coarseMass distribution (samplingView dataStructure) selectedView
      let successMassAt := successMass distribution (samplingView dataStructure)
        (samplingSuccess dataStructure inputDistribution queryDistribution)
        selectedView
      have hmass : 0 ≤ mass := by
        dsimp [mass]
        exact coarseMass_nonnegative distribution (samplingView dataStructure)
          selectedView
      by_cases hgood : baseline * mass ≤ successMassAt
      · have hrawGood : baseline *
            coarseMass distribution (samplingView dataStructure) selectedView ≤
          successMass distribution (samplingView dataStructure)
            (samplingSuccess dataStructure inputDistribution queryDistribution)
            selectedView := by
          simpa [mass, successMassAt] using hgood
        by_cases hpositive : 0 < mass
        · have hquantitative :
              QuantitativeGoodView dataStructure inputDistribution
                queryDistribution p hp.le hpone selectedView := by
            refine ⟨?_, ?_⟩
            · simpa [mass] using hpositive
            · simpa [baseline, updated] using hrawGood
          simp [hrawGood, hquantitative]
        · have hzero : mass = 0 :=
            le_antisymm (le_of_not_gt hpositive) hmass
          have hnotQuantitative :
              ¬ QuantitativeGoodView dataStructure inputDistribution
                queryDistribution p hp.le hpone selectedView := by
            intro hquantitative
            exact hpositive (by simpa [mass] using hquantitative.1)
          have hcoarseZero :
              coarseMass distribution (samplingView dataStructure)
                selectedView = 0 := by
            simpa [mass] using hzero
          simp [hnotQuantitative, hcoarseZero]
      · have hrawNotGood : ¬ (baseline *
            coarseMass distribution (samplingView dataStructure) selectedView ≤
          successMass distribution (samplingView dataStructure)
            (samplingSuccess dataStructure inputDistribution queryDistribution)
            selectedView) := by
          simpa [mass, successMassAt] using hgood
        have hnotQuantitative :
            ¬ QuantitativeGoodView dataStructure inputDistribution
              queryDistribution p hp.le hpone selectedView := by
          intro hquantitative
          exact hrawNotGood (by simpa [baseline, updated] using hquantitative.2)
        simp [hrawNotGood, hnotQuantitative]
    _ = ∑ selectedView : SamplingView Query wordBits cacheCells,
        if QuantitativeGoodView dataStructure inputDistribution
          queryDistribution p hp.le (hhalf.trans (by norm_num)) selectedView
        then coarseMass
          (samplingExperimentDistribution (wordBits := wordBits)
            inputDistribution queryDistribution p hp.le
              (hhalf.trans (by norm_num)))
          (samplingView dataStructure) selectedView
        else 0 := by rfl

theorem peakBaseline_mul_fiberReward_le_selectedFiberSum
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
          (selector selectedView)) :
    samplingPeakBaseline
        (dataStructure.expectedUpdatedProbes
          inputDistribution queryDistribution) p *
      fiberReward dataStructure inputDistribution queryDistribution p ≤
    ∑ selectedView : SamplingView Query wordBits cacheCells,
      coarseMass
          (samplingExperimentDistribution (wordBits := wordBits)
            inputDistribution queryDistribution p hp.le
              (hhalf.trans (by norm_num)))
          (samplingView dataStructure) selectedView *
        fiberL1
          (experimentPosterior dataStructure problem inputDistribution
            queryDistribution p hp.le (hhalf.trans (by norm_num)) selectedView)
          (selector selectedView) := by
  classical
  let hpone : p ≤ (1 : ℝ) := hhalf.trans (by norm_num)
  let distribution := samplingExperimentDistribution (wordBits := wordBits)
    inputDistribution queryDistribution p hp.le hpone
  let eligible := QuantitativeGoodView dataStructure inputDistribution
    queryDistribution p hp.le hpone
  let mass : SamplingView Query wordBits cacheCells → ℝ :=
    fun selectedView ↦ coarseMass distribution (samplingView dataStructure)
      selectedView
  let reward : (selectedView : SamplingView Query wordBits cacheCells) →
      Finset (Fin (simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card) → ℝ :=
    fun selectedView coordinates ↦ fiberL1
      (experimentPosterior dataStructure problem inputDistribution
        queryDistribution p hp.le hpone selectedView) coordinates
  let lower := fiberReward dataStructure inputDistribution queryDistribution p
  let baseline := samplingPeakBaseline
    (dataStructure.expectedUpdatedProbes inputDistribution queryDistribution) p
  have hmassNonnegative : ∀ selectedView, 0 ≤ mass selectedView := by
    intro selectedView
    dsimp [mass]
    exact coarseMass_nonnegative distribution (samplingView dataStructure)
      selectedView
  have hlowerNonnegative : 0 ≤ lower := by
    dsimp [lower, fiberReward]
    positivity
  have heligibleMass : baseline ≤
      ∑ selectedView, if eligible selectedView then mass selectedView else 0 := by
    simpa [baseline, eligible, mass, distribution, hpone] using
      samplingPeakBaseline_le_quantitativeGoodViewMass dataStructure
        inputDistribution queryDistribution p hp hhalf
  have hrestricted : lower *
      (∑ selectedView, if eligible selectedView then mass selectedView else 0) ≤
      ∑ selectedView, if eligible selectedView then
        mass selectedView * reward selectedView (selector selectedView) else 0 := by
    apply lower_mul_eligibleMass_le_selectedReward
      (fun selectedView : SamplingView Query wordBits cacheCells ↦
        (simulatedAddresses dataStructure
          selectedView.1.1 selectedView.2).card)
      eligible mass hmassNonnegative lower reward selector
    intro selectedView heligible
    exact hselector selectedView heligible
  calc
    baseline * lower = lower * baseline := by ring
    _ ≤ lower *
        (∑ selectedView, if eligible selectedView then mass selectedView else 0) :=
      mul_le_mul_of_nonneg_left heligibleMass hlowerNonnegative
    _ ≤ ∑ selectedView, if eligible selectedView then
        mass selectedView * reward selectedView (selector selectedView) else 0 :=
      hrestricted
    _ ≤ ∑ selectedView, mass selectedView *
        reward selectedView (selector selectedView) := by
      apply Finset.sum_le_sum
      intro selectedView _hselectedView
      by_cases heligible : eligible selectedView
      · simp [heligible]
      · simp only [heligible, if_false]
        exact mul_nonneg (hmassNonnegative selectedView)
          (fiberL1_nonneg _ _)
    _ = ∑ selectedView : SamplingView Query wordBits cacheCells,
      coarseMass
          (samplingExperimentDistribution (wordBits := wordBits)
            inputDistribution queryDistribution p hp.le
              (hhalf.trans (by norm_num)))
          (samplingView dataStructure) selectedView *
        fiberL1
          (experimentPosterior dataStructure problem inputDistribution
            queryDistribution p hp.le (hhalf.trans (by norm_num)) selectedView)
          (selector selectedView) := by rfl

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuSelectedReward
