import PegSeparation.CFLNotPEG.External.LarsenYuExperimentPosterior


namespace PegSeparation.External.LarsenYuExperimentPeak

noncomputable section

open LarsenYuExperimentPosterior LarsenYuPosteriorFiltering
  LarsenYuBaseView PeakToAverage
  LarsenYuExperimentPosterior.CellProbe.StaticStructure
  LarsenYuBaseView.CellProbe.StaticStructure

namespace CellProbe.StaticStructure

variable {Input Query : Type} [Fintype Input] [Fintype Query]
  {wordBits cacheCells maxUpdatedCells : Nat}

local instance samplingViewDecidableEq
    (Query : Type) (wordBits cacheCells : Nat) :
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


def indexedExperimentContent
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selectedView : SamplingView Query wordBits cacheCells)
    (sample : SamplingExperiment Input Query wordBits) :
    Fin (simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).card → CellProbe.Word wordBits :=
  fun index ↦ experimentContent dataStructure selectedView sample
    ((simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).equivFin.symm index)

def indexedExperimentPeak
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selectedView : SamplingView Query wordBits cacheCells) :
    Fin (simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).card → CellProbe.Word wordBits :=
  fun index ↦ experimentPeak dataStructure selectedView
    ((simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).equivFin.symm index)

theorem samplingSuccess_implies_indexedExperimentContent_eq_peak
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (sample : SamplingExperiment Input Query wordBits)
    (selectedView : SamplingView Query wordBits cacheCells)
    (hview : samplingView dataStructure sample = selectedView)
    (hsuccess : samplingSuccess dataStructure inputDistribution
      queryDistribution sample) :
    indexedExperimentContent dataStructure selectedView sample =
      indexedExperimentPeak dataStructure selectedView := by
  have hpeak := samplingSuccess_implies_experimentContent_eq_peak
    dataStructure inputDistribution queryDistribution sample selectedView
      hview hsuccess
  funext index
  exact congrFun hpeak
    ((simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).equivFin.symm index)

theorem experimentContent_eq_peak_of_indexed_eq
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (sample : SamplingExperiment Input Query wordBits)
    (selectedView : SamplingView Query wordBits cacheCells)
    (hcontent : indexedExperimentContent dataStructure selectedView sample =
      indexedExperimentPeak dataStructure selectedView) :
    experimentContent dataStructure selectedView sample =
      experimentPeak dataStructure selectedView := by
  funext address
  have hindexed := congrFun hcontent
    ((simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).equivFin address)
  simpa [indexedExperimentContent, indexedExperimentPeak] using hindexed

theorem problemSignal_eq_peakSignal_of_indexedContent_eq
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (hsolves : dataStructure.Solves problem)
    (sample : SamplingExperiment Input Query wordBits)
    (selectedView : SamplingView Query wordBits cacheCells)
    (hview : samplingView dataStructure sample = selectedView)
    (hcontent : indexedExperimentContent dataStructure selectedView sample =
      indexedExperimentPeak dataStructure selectedView) :
    problemSignal problem sample = peakSignal dataStructure selectedView := by
  apply problemSignal_eq_peakSignal_of_content_eq
    dataStructure problem hsolves sample selectedView hview
  exact experimentContent_eq_peak_of_indexed_eq dataStructure sample
    selectedView hcontent

theorem exists_large_experimentPosteriorFiberL1_of_goodView
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (hsolves : dataStructure.Solves problem)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (selectedView : SamplingView Query wordBits cacheCells)
    {degree : Nat} {M baseline : ℝ}
    (certificate : AndCertificate
      (simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card degree M)
    (hviewPositive : 0 <
      coarseMass
        (samplingExperimentDistribution (wordBits := wordBits)
          inputDistribution queryDistribution p hp hpone)
        (samplingView dataStructure) selectedView)
    (hbaselinePositive : 0 < baseline)
    (hgood : baseline *
        coarseMass
          (samplingExperimentDistribution (wordBits := wordBits)
            inputDistribution queryDistribution p hp hpone)
          (samplingView dataStructure) selectedView ≤
      successMass
        (samplingExperimentDistribution (wordBits := wordBits)
          inputDistribution queryDistribution p hp hpone)
        (samplingView dataStructure)
        (samplingSuccess dataStructure inputDistribution queryDistribution)
        selectedView)
    (hscale : 2 ≤ M * baseline) :
    ∃ coordinates : Finset (Fin
        (simulatedAddresses dataStructure
          selectedView.1.1 selectedView.2).card),
      coordinates.card ≤ degree ∧
        1 ≤ certificate.coefficientL1 *
          fiberL1
            (normalizedSignedContent
              (samplingExperimentDistribution (wordBits := wordBits)
                inputDistribution queryDistribution p hp hpone)
              (samplingView dataStructure)
              (indexedExperimentContent dataStructure selectedView)
              (problemSignal problem) selectedView)
            coordinates := by
  apply exists_large_posteriorFiberL1_of_goodView
    (fixedSignal := peakSignal dataStructure selectedView)
    certificate
    (samplingExperimentDistribution (wordBits := wordBits)
      inputDistribution queryDistribution p hp hpone)
    (samplingView dataStructure)
    (indexedExperimentContent dataStructure selectedView)
    (problemSignal problem)
    (samplingSuccess dataStructure inputDistribution queryDistribution)
    selectedView
    (indexedExperimentPeak dataStructure selectedView)
    hviewPositive hbaselinePositive
  · intro sample
    rw [abs_problemSignal]
  · exact hgood
  · intro sample hview hsuccess
    exact samplingSuccess_implies_indexedExperimentContent_eq_peak
      dataStructure inputDistribution queryDistribution sample selectedView
        hview hsuccess
  · exact abs_peakSignal dataStructure selectedView
  · intro sample hview hcontent
    exact problemSignal_eq_peakSignal_of_indexedContent_eq
      dataStructure problem hsolves sample selectedView hview hcontent
  · exact hscale

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuExperimentPeak
