import PegSeparation.CFLNotPEG.External.LarsenYuCoordinateSelector
import PegSeparation.CFLNotPEG.External.LarsenYuGoodViewTrace
import PegSeparation.CFLNotPEG.External.LarsenYuPeakQuantitative
import PegSeparation.CFLNotPEG.External.LarsenYuUpperBounds


namespace PegSeparation.External.LarsenYuQuantitativeSelector

noncomputable section

open LarsenYuBernoulli LarsenYuPosteriorFiltering
  LarsenYuExperimentPosterior LarsenYuExperimentPeak LarsenYuBaseView
  LarsenYuGoodViewTrace LarsenYuCoordinateSelector
  LarsenYuPeakQuantitative PeakToAverage
  LarsenYuExperimentPosterior.CellProbe.StaticStructure
  LarsenYuExperimentPeak.CellProbe.StaticStructure
  LarsenYuBaseView.CellProbe.StaticStructure
  LarsenYuGoodViewTrace.CellProbe.StaticStructure

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

def coordinateBudget
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) (p : ℝ) : ℝ :=
  let total := dataStructure.expectedTotalProbes
    inputDistribution queryDistribution
  let updated := dataStructure.expectedUpdatedProbes
    inputDistribution queryDistribution
  96 * (Real.sqrt (total * samplingLambda updated p) +
    samplingLambda updated p)

def fiberReward
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) (p : ℝ) : ℝ :=
  let total := dataStructure.expectedTotalProbes
    inputDistribution queryDistribution
  let updated := dataStructure.expectedUpdatedProbes
    inputDistribution queryDistribution
  Real.rpow 2
    (-384 * (Real.sqrt (total * samplingLambda updated p) +
      samplingLambda updated p) * samplingLogFactor p)

def experimentPosterior
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (selectedView : SamplingView Query wordBits cacheCells) :
    (Fin (simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).card → CellProbe.Word wordBits) → ℝ :=
  normalizedSignedContent
    (samplingExperimentDistribution (wordBits := wordBits)
      inputDistribution queryDistribution p hp hpone)
    (samplingView dataStructure)
    (indexedExperimentContent dataStructure selectedView)
    (problemSignal problem) selectedView

def QuantitativeGoodView
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (selectedView : SamplingView Query wordBits cacheCells) : Prop :=
  let distribution := samplingExperimentDistribution (wordBits := wordBits)
    inputDistribution queryDistribution p hp hpone
  let updated := dataStructure.expectedUpdatedProbes
    inputDistribution queryDistribution
  0 < coarseMass distribution (samplingView dataStructure) selectedView ∧
    samplingPeakBaseline updated p *
        coarseMass distribution (samplingView dataStructure) selectedView ≤
      successMass distribution (samplingView dataStructure)
        (samplingSuccess dataStructure inputDistribution queryDistribution)
        selectedView

local instance quantitativeGoodViewDecidable
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1) :
    DecidablePred (QuantitativeGoodView dataStructure inputDistribution
      queryDistribution p hp hpone) :=
  fun _ ↦ Classical.propDecidable _

theorem exists_coordinates_of_quantitativeGoodView
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (hsolves : dataStructure.Solves problem)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 < p) (hhalf : p ≤ 1 / 2)
    (selectedView : SamplingView Query wordBits cacheCells)
    (hgoodView : QuantitativeGoodView dataStructure inputDistribution
      queryDistribution p hp.le (hhalf.trans (by norm_num)) selectedView) :
    ∃ coordinates : Finset (Fin (simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card),
      (coordinates.card : ℝ) ≤
          coordinateBudget dataStructure inputDistribution queryDistribution p ∧
        fiberReward dataStructure inputDistribution queryDistribution p ≤
          fiberL1
            (experimentPosterior dataStructure problem inputDistribution
              queryDistribution p hp.le (hhalf.trans (by norm_num)) selectedView)
            coordinates := by
  classical
  let hpone : p ≤ (1 : ℝ) := hhalf.trans (by norm_num)
  let distribution := samplingExperimentDistribution (wordBits := wordBits)
    inputDistribution queryDistribution p hp.le hpone
  let view := samplingView dataStructure
  let content := indexedExperimentContent dataStructure selectedView
  let signal : SamplingExperiment Input Query wordBits → ℝ :=
    problemSignal (wordBits := wordBits) problem
  let success := samplingSuccess dataStructure inputDistribution queryDistribution
  let peak := indexedExperimentPeak dataStructure selectedView
  let total := dataStructure.expectedTotalProbes
    inputDistribution queryDistribution
  let updated := dataStructure.expectedUpdatedProbes
    inputDistribution queryDistribution
  have htotal : 0 ≤ total := by
    dsimp [total]
    exact dataStructure.expectedTotalProbes_nonneg
      inputDistribution queryDistribution
  have hupdated : 0 ≤ updated := by
    dsimp [updated]
    exact dataStructure.expectedUpdatedProbes_nonneg
      inputDistribution queryDistribution
  have hbaseline : 0 < samplingPeakBaseline updated p :=
    samplingPeakBaseline_pos updated hp
  have hdimension :
      ((simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card : ℝ) ≤ 4 * total := by
    apply simulatedAddresses_card_le_four_expectedTotal_of_goodView
      dataStructure inputDistribution queryDistribution p hp.le hpone
      selectedView (samplingPeakBaseline updated p) hbaseline
    · exact hgoodView.1
    · exact hgoodView.2
  have hfL1 :
      (∑ point, |normalizedSignedContent distribution view content signal
        selectedView point|) ≤ 1 := by
    apply sum_abs_normalizedSignedContent_le_one
      distribution view content signal selectedView hgoodView.1
    intro sample
    rw [abs_problemSignal]
  have hfpeak : samplingPeakBaseline updated p ≤
      |normalizedSignedContent distribution view content signal
        selectedView peak| := by
    apply baseline_le_abs_normalizedSignedContent_peak
      (fixedSignal := peakSignal dataStructure selectedView)
      distribution view content signal success selectedView peak
      (samplingPeakBaseline updated p) hgoodView.1 hgoodView.2
    · intro sample hsampleView hsampleSuccess
      exact samplingSuccess_implies_indexedExperimentContent_eq_peak
        dataStructure inputDistribution queryDistribution sample selectedView
          hsampleView hsampleSuccess
    · exact abs_peakSignal dataStructure selectedView
    · intro sample hsampleView hsampleContent
      exact problemSignal_eq_peakSignal_of_indexedContent_eq
        dataStructure problem hsolves sample selectedView hsampleView
          hsampleContent
  obtain ⟨coordinates, hcard, hfiber⟩ :=
    exists_fiberL1_samplingPeak_of_dimension_le_four_total
      hupdated hp hhalf htotal hdimension
      (normalizedSignedContent distribution view content signal selectedView)
      peak hfL1 hfpeak
  refine ⟨coordinates, ?_, ?_⟩
  · simpa [coordinateBudget, total, updated] using hcard
  · simpa [fiberReward, experimentPosterior, distribution, view, content,
      signal, total, updated, hpone] using hfiber

theorem exists_quantitativeCoordinateSelector
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (hsolves : dataStructure.Solves problem)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    ∃ selector : (selectedView : SamplingView Query wordBits cacheCells) →
        Finset (Fin (simulatedAddresses dataStructure
          selectedView.1.1 selectedView.2).card),
      (∀ selectedView, (selector selectedView).card ≤
        ⌈coordinateBudget dataStructure inputDistribution
          queryDistribution p⌉₊) ∧
      ∀ selectedView,
        QuantitativeGoodView dataStructure inputDistribution queryDistribution
          p hp.le (hhalf.trans (by norm_num)) selectedView →
        fiberReward dataStructure inputDistribution queryDistribution p ≤
          fiberL1
            (experimentPosterior dataStructure problem inputDistribution
              queryDistribution p hp.le (hhalf.trans (by norm_num)) selectedView)
            (selector selectedView) := by
  apply exists_dependentSelector
    (fun selectedView : SamplingView Query wordBits cacheCells ↦
      (simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card)
    (QuantitativeGoodView dataStructure inputDistribution queryDistribution
      p hp.le (hhalf.trans (by norm_num)))
    (coordinateBudget dataStructure inputDistribution queryDistribution p)
    (fiberReward dataStructure inputDistribution queryDistribution p)
    (fun selectedView coordinates ↦
      fiberL1
        (experimentPosterior dataStructure problem inputDistribution
          queryDistribution p hp.le (hhalf.trans (by norm_num)) selectedView)
        coordinates)
  intro selectedView hgoodView
  exact exists_coordinates_of_quantitativeGoodView dataStructure problem
    hsolves inputDistribution queryDistribution p hp hhalf selectedView hgoodView

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuQuantitativeSelector
