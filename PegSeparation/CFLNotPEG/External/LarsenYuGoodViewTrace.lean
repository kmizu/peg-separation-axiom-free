import PegSeparation.CFLNotPEG.External.LarsenYuExperimentPeak


namespace PegSeparation.External.LarsenYuGoodViewTrace

noncomputable section

open LarsenYuPosteriorFiltering LarsenYuGoodSampling LarsenYuJointCosts
  LarsenYuExperimentPosterior LarsenYuBaseView
  LarsenYuExperimentPosterior.CellProbe.StaticStructure
  LarsenYuGoodSampling.CellProbe.StaticStructure
  LarsenYuJointCosts.CellProbe.StaticStructure
  LarsenYuBaseView.CellProbe.StaticStructure
  LarsenYuSimulationCorrectness.CellProbe.StaticStructure

theorem exists_of_successMass_pos
    {Input View : Type} [Fintype Input] [Fintype View] [DecidableEq View]
    (distribution : FiniteDistribution Input) (view : Input → View)
    (success : Input → Prop) [DecidablePred success]
    (selectedView : View)
    (hpositive : 0 < successMass distribution view success selectedView) :
    ∃ input, view input = selectedView ∧ success input := by
  classical
  by_contra hnone
  push Not at hnone
  have hzero : successMass distribution view success selectedView = 0 := by
    unfold successMass
    apply Finset.sum_eq_zero
    intro input _hinput
    by_cases hview : view input = selectedView
    · have hnot := hnone input hview
      simp [hview, hnot]
    · simp [hview]
  linarith

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

theorem simulatedAddresses_card_le_four_expectedTotal_of_success
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (sample : SamplingExperiment Input Query wordBits)
    (selectedView : SamplingView Query wordBits cacheCells)
    (hview : samplingView dataStructure sample = selectedView)
    (hsuccess : samplingSuccess dataStructure inputDistribution
      queryDistribution sample) :
    ((simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).card : ℝ) ≤
        4 * dataStructure.expectedTotalProbes
          inputDistribution queryDistribution := by
  rcases sample with ⟨⟨input, query⟩, mask⟩
  rcases selectedView with ⟨⟨selectedQuery, selectedMask⟩, view⟩
  simp only [samplingView, Prod.mk.injEq] at hview
  rcases hview with ⟨⟨rfl, rfl⟩, hbase⟩
  subst view
  have hsimulation :
      simulateFromBaseView dataStructure query
          (baseView dataStructure mask input) =
        dataStructure.execute input query := by
    rw [simulateFrom_generated_baseView]
    exact run_sampledMemory_eq_execute_of_includes
      dataStructure input query mask hsuccess.2
  have hcardNat :
      (simulatedAddresses dataStructure query
        (baseView dataStructure mask input)).card ≤
      (dataStructure.execute input query).2.length := by
    calc
      (simulatedAddresses dataStructure query
          (baseView dataStructure mask input)).card =
          (simulateFromBaseView dataStructure query
            (baseView dataStructure mask input)).2.toFinset.card := rfl
      _ ≤ (simulateFromBaseView dataStructure query
          (baseView dataStructure mask input)).2.length :=
        List.toFinset_card_le _
      _ = (dataStructure.execute input query).2.length := by
        rw [hsimulation]
  have hcost :
      jointTotalCost dataStructure (input, query) ≤
        4 * dataStructure.expectedTotalProbes
          inputDistribution queryDistribution := by
    unfold samplingSuccess at hsuccess
    unfold GoodCost BadCost at hsuccess
    push Not at hsuccess
    exact hsuccess.1.1
  have hcast :
      ((simulatedAddresses dataStructure query
        (baseView dataStructure mask input)).card : ℝ) ≤
      ((dataStructure.execute input query).2.length : ℝ) := by
    exact_mod_cast hcardNat
  exact hcast.trans (by simpa [jointTotalCost, CellProbe.StaticStructure.probeTrace] using hcost)

theorem simulatedAddresses_card_le_four_expectedTotal_of_goodView
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (selectedView : SamplingView Query wordBits cacheCells)
    (baseline : ℝ) (hbaseline : 0 < baseline)
    (hviewPositive : 0 <
      coarseMass
        (samplingExperimentDistribution (wordBits := wordBits)
          inputDistribution queryDistribution p hp hpone)
        (samplingView dataStructure) selectedView)
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
        selectedView) :
    ((simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).card : ℝ) ≤
        4 * dataStructure.expectedTotalProbes
          inputDistribution queryDistribution := by
  have hsuccessPositive : 0 <
      successMass
        (samplingExperimentDistribution (wordBits := wordBits)
          inputDistribution queryDistribution p hp hpone)
        (samplingView dataStructure)
        (samplingSuccess dataStructure inputDistribution queryDistribution)
        selectedView :=
    (mul_pos hbaseline hviewPositive).trans_le hgood
  obtain ⟨sample, hview, hsuccess⟩ := exists_of_successMass_pos
    (samplingExperimentDistribution (wordBits := wordBits)
      inputDistribution queryDistribution p hp hpone)
    (samplingView dataStructure)
    (samplingSuccess dataStructure inputDistribution queryDistribution)
    selectedView hsuccessPositive
  exact simulatedAddresses_card_le_four_expectedTotal_of_success
    dataStructure inputDistribution queryDistribution sample selectedView
      hview hsuccess

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuGoodViewTrace
