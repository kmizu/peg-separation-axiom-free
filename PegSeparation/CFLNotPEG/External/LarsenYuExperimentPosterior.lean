import PegSeparation.CFLNotPEG.External.LarsenYuBaseView
import PegSeparation.CFLNotPEG.External.LarsenYuGoodSampling
import PegSeparation.CFLNotPEG.External.LarsenYuPosteriorFiltering


open scoped BigOperators

namespace PegSeparation.External.LarsenYuExperimentPosterior

noncomputable section

open LarsenYuBernoulli LarsenYuBernoulliEvents LarsenYuJointCosts
  LarsenYuGoodSampling LarsenYuPosteriorFiltering LarsenYuBaseView
  LarsenYuSampledUpdated
  LarsenYuSampledUpdated.CellProbe.StaticStructure
  LarsenYuGoodSampling.CellProbe.StaticStructure
  LarsenYuBaseView.CellProbe.StaticStructure

abbrev SamplingExperiment
    (Input Query : Type) (wordBits : Nat) :=
  (Input × Query) × Mask (CellProbe.Address wordBits)

abbrev SamplingView
    (Query : Type) (wordBits cacheCells : Nat) :=
  (Query × Mask (CellProbe.Address wordBits)) ×
    BaseView wordBits cacheCells

namespace CellProbe.StaticStructure

variable {Input Query : Type} [Fintype Input] [Fintype Query]

local instance samplingViewDecidableEq
    (Query : Type) (wordBits cacheCells : Nat) :
    DecidableEq (SamplingView Query wordBits cacheCells) :=
  Classical.decEq _

variable {wordBits cacheCells maxUpdatedCells : Nat}

def samplingExperimentDistribution
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1) :
    FiniteDistribution (SamplingExperiment Input Query wordBits) :=
  productDistribution (Input × Query) (Mask (CellProbe.Address wordBits))
    (productDistribution Input Query inputDistribution queryDistribution)
    (maskDistribution (CellProbe.Address wordBits) p hp hpone)

def samplingSuccess
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (sample : SamplingExperiment Input Query wordBits) : Prop :=
  GoodCost dataStructure inputDistribution queryDistribution sample.1 ∧
    Includes sample.2
      (probedUpdatedAddresses dataStructure sample.1.1 sample.1.2)

local instance samplingSuccessDecidable
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    DecidablePred
      (samplingSuccess dataStructure inputDistribution queryDistribution) :=
  fun _ ↦ Classical.propDecidable _

theorem eventMass_samplingSuccess_eq_jointGoodSamplingMass
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1) :
    eventMass
        (samplingExperimentDistribution inputDistribution queryDistribution
          p hp hpone)
        (samplingSuccess dataStructure inputDistribution queryDistribution) =
      jointGoodSamplingMass dataStructure inputDistribution queryDistribution
        p hp hpone := by
  classical
  unfold eventMass samplingExperimentDistribution productDistribution
    samplingSuccess jointGoodSamplingMass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro pair _hpair
  by_cases hgood :
      GoodCost dataStructure inputDistribution queryDistribution pair
  · simp only [hgood, true_and, if_true, mul_one]
    unfold productDistribution eventMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro mask _hmask
    ring_nf
  · simp [hgood]

theorem half_rpow_expectedUpdated_le_samplingSuccessMass
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 < p) (hpone : p ≤ 1) :
    (1 / 2 : ℝ) * Real.rpow p
        (4 * dataStructure.expectedUpdatedProbes
          inputDistribution queryDistribution) ≤
      eventMass
        (samplingExperimentDistribution inputDistribution queryDistribution
          p hp.le hpone)
        (samplingSuccess dataStructure inputDistribution queryDistribution) := by
  rw [eventMass_samplingSuccess_eq_jointGoodSamplingMass]
  exact half_rpow_expectedUpdated_le_jointGoodSamplingMass dataStructure
    inputDistribution queryDistribution p hp hpone

def samplingView
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (sample : SamplingExperiment Input Query wordBits) :
    SamplingView Query wordBits cacheCells :=
  ((sample.1.2, sample.2),
    baseView dataStructure sample.2 sample.1.1)

theorem half_globalBaseline_le_goodSamplingViewMass
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 < p) (hpone : p ≤ 1) :
    let distribution := samplingExperimentDistribution
      (wordBits := wordBits) inputDistribution queryDistribution p hp.le hpone
    let baseline := (1 / 2 : ℝ) * Real.rpow p
      (4 * dataStructure.expectedUpdatedProbes
        inputDistribution queryDistribution)
    baseline / 2 ≤
      ∑ selectedView : SamplingView Query wordBits cacheCells,
        if baseline / 2 *
            coarseMass distribution (samplingView dataStructure) selectedView ≤
          successMass distribution (samplingView dataStructure)
            (samplingSuccess dataStructure inputDistribution queryDistribution)
            selectedView
        then coarseMass distribution (samplingView dataStructure) selectedView
        else 0 := by
  classical
  dsimp only
  apply half_baseline_le_goodFiberMass
  · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hp.le _)
  · exact coarseMass_nonnegative _ _
  · exact sum_coarseMass _ _
  · exact successMass_le_coarseMass _ _ _
  · rw [sum_successMass]
    simpa [eventMass] using
      (half_rpow_expectedUpdated_le_samplingSuccessMass dataStructure
        inputDistribution queryDistribution p hp hpone)

def experimentContent
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selectedView : SamplingView Query wordBits cacheCells)
    (sample : SamplingExperiment Input Query wordBits) :
    ↑(simulatedAddresses dataStructure selectedView.1.1 selectedView.2) →
      CellProbe.Word wordBits :=
  trueContent dataStructure
    (simulatedAddresses dataStructure selectedView.1.1 selectedView.2)
    sample.1.1

def experimentPeak
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selectedView : SamplingView Query wordBits cacheCells) :
    ↑(simulatedAddresses dataStructure selectedView.1.1 selectedView.2) →
      CellProbe.Word wordBits :=
  usedContent dataStructure selectedView.1.1 selectedView.2

theorem samplingSuccess_implies_experimentContent_eq_peak
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (sample : SamplingExperiment Input Query wordBits)
    (selectedView : SamplingView Query wordBits cacheCells)
    (hview : samplingView dataStructure sample = selectedView)
    (hsuccess : samplingSuccess dataStructure inputDistribution
      queryDistribution sample) :
    experimentContent dataStructure selectedView sample =
      experimentPeak dataStructure selectedView := by
  rcases sample with ⟨⟨input, query⟩, mask⟩
  rcases selectedView with ⟨⟨selectedQuery, selectedMask⟩, view⟩
  simp only [samplingView, Prod.mk.injEq] at hview
  rcases hview with ⟨⟨rfl, rfl⟩, hbase⟩
  subst view
  exact trueContent_eq_usedContent_of_includes dataStructure mask input query
    hsuccess.2

def problemSignal
    (problem : BinaryProblem Input Query)
    (sample : SamplingExperiment Input Query wordBits) : ℝ :=
  if problem.value sample.1.2 sample.1.1 then 1 else -1

omit [Fintype Input] [Fintype Query] in
theorem abs_problemSignal (problem : BinaryProblem Input Query)
    (sample : SamplingExperiment Input Query wordBits) :
    |problemSignal problem sample| = 1 := by
  cases hvalue : problem.value sample.1.2 sample.1.1 <;>
    simp [problemSignal, hvalue]

def peakSignal
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selectedView : SamplingView Query wordBits cacheCells) : ℝ :=
  if (simulateFromBaseView dataStructure selectedView.1.1 selectedView.2).1
    then 1 else -1

omit [Fintype Input] [Fintype Query] in
theorem abs_peakSignal
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selectedView : SamplingView Query wordBits cacheCells) :
    |peakSignal dataStructure selectedView| = 1 := by
  cases hanswer :
      (simulateFromBaseView dataStructure selectedView.1.1 selectedView.2).1 <;>
    simp [peakSignal, hanswer]

theorem problemSignal_eq_peakSignal_of_content_eq
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (hsolves : dataStructure.Solves problem)
    (sample : SamplingExperiment Input Query wordBits)
    (selectedView : SamplingView Query wordBits cacheCells)
    (hview : samplingView dataStructure sample = selectedView)
    (hcontent : experimentContent dataStructure selectedView sample =
      experimentPeak dataStructure selectedView) :
    problemSignal problem sample = peakSignal dataStructure selectedView := by
  rcases sample with ⟨⟨input, query⟩, mask⟩
  rcases selectedView with ⟨⟨selectedQuery, selectedMask⟩, view⟩
  simp only [samplingView, Prod.mk.injEq] at hview
  rcases hview with ⟨⟨rfl, rfl⟩, hbase⟩
  have hvalue := problemValue_eq_simulatedAnswer_of_peakContent
    dataStructure problem hsolves mask input query view hbase hcontent
  unfold problemSignal peakSignal
  rw [hvalue]

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuExperimentPosterior
