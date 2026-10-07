import PegSeparation.CFLNotPEG.External.LarsenYuJointCosts
import PegSeparation.CFLNotPEG.External.LarsenYuSampledUpdated


open scoped BigOperators

namespace PegSeparation.External.LarsenYuGoodSampling

noncomputable section

open LarsenYuBernoulli LarsenYuBernoulliEvents LarsenYuJointCosts
  LarsenYuJointCosts.CellProbe.StaticStructure LarsenYuSampledUpdated
  LarsenYuSampledUpdated.CellProbe.StaticStructure

namespace CellProbe.StaticStructure

variable {Input Query : Type} [Fintype Input] [Fintype Query]
  {wordBits cacheCells maxUpdatedCells : Nat}

def BadCost
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (pair : Input × Query) : Prop :=
  4 * dataStructure.expectedTotalProbes inputDistribution queryDistribution <
      jointTotalCost dataStructure pair ∨
    4 * dataStructure.expectedUpdatedProbes inputDistribution queryDistribution <
      jointUpdatedCost dataStructure pair

def GoodCost
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (pair : Input × Query) : Prop :=
  ¬ BadCost dataStructure inputDistribution queryDistribution pair

local instance badCostDecidable
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    DecidablePred (BadCost dataStructure inputDistribution queryDistribution) :=
  fun _ ↦ Classical.propDecidable _

local instance goodCostDecidable
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    DecidablePred (GoodCost dataStructure inputDistribution queryDistribution) :=
  fun _ ↦ Classical.propDecidable _

local instance includesDecidable {Coordinate : Type} [Fintype Coordinate]
    [DecidableEq Coordinate] (mask : Mask Coordinate)
    (required : Finset Coordinate) : Decidable (Includes mask required) := by
  unfold Includes
  infer_instance

theorem goodCost_eventMass_ge_half
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    (1 / 2 : ℝ) ≤
      eventMass
        (productDistribution Input Query inputDistribution queryDistribution)
        (GoodCost dataStructure inputDistribution queryDistribution) := by
  let distribution :=
    productDistribution Input Query inputDistribution queryDistribution
  let bad := BadCost dataStructure inputDistribution queryDistribution
  let good := GoodCost dataStructure inputDistribution queryDistribution
  have hbadEq : eventMass distribution bad =
      eventMass distribution (fun pair ↦
        4 * dataStructure.expectedTotalProbes
            inputDistribution queryDistribution <
          jointTotalCost dataStructure pair ∨
        4 * dataStructure.expectedUpdatedProbes
            inputDistribution queryDistribution <
          jointUpdatedCost dataStructure pair) := by
    unfold eventMass
    apply Finset.sum_congr rfl
    intro pair _hpair
    by_cases hbadPair : bad pair
    · have hraw :
          4 * dataStructure.expectedTotalProbes
              inputDistribution queryDistribution <
            jointTotalCost dataStructure pair ∨
          4 * dataStructure.expectedUpdatedProbes
              inputDistribution queryDistribution <
            jointUpdatedCost dataStructure pair := by
        simpa [bad, BadCost] using hbadPair
      simp [hbadPair, hraw]
    · have hraw : ¬ (
          4 * dataStructure.expectedTotalProbes
              inputDistribution queryDistribution <
            jointTotalCost dataStructure pair ∨
          4 * dataStructure.expectedUpdatedProbes
              inputDistribution queryDistribution <
            jointUpdatedCost dataStructure pair) := by
        simpa [bad, BadCost] using hbadPair
      simp [hbadPair, hraw]
  have hbad : eventMass distribution bad ≤ (1 / 2 : ℝ) := by
    rw [hbadEq]
    simpa [distribution] using
      (joint_bad_cost_mass_le_half dataStructure inputDistribution
        queryDistribution)
  have hpartition : eventMass distribution good + eventMass distribution bad = 1 := by
    unfold eventMass
    rw [← Finset.sum_add_distrib]
    calc
      (∑ pair, (distribution.mass pair * (if good pair then 1 else 0) +
          distribution.mass pair * (if bad pair then 1 else 0))) =
          ∑ pair, distribution.mass pair := by
        apply Finset.sum_congr rfl
        intro pair _hpair
        by_cases hbadPair : bad pair <;>
          simp [good, GoodCost, bad, hbadPair]
      _ = 1 := distribution.mass_sum
  linarith

theorem rpow_expectedUpdated_le_maskSuccess_of_good
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (pair : Input × Query)
    (p : ℝ) (hp : 0 < p) (hpone : p ≤ 1)
    (hgood : GoodCost dataStructure inputDistribution queryDistribution pair) :
    Real.rpow p
        (4 * dataStructure.expectedUpdatedProbes
          inputDistribution queryDistribution) ≤
      eventMass
        (maskDistribution (CellProbe.Address wordBits) p hp.le hpone)
        (fun mask ↦ Includes mask
          (probedUpdatedAddresses dataStructure pair.1 pair.2)) := by
  have hupdated : jointUpdatedCost dataStructure pair ≤
      4 * dataStructure.expectedUpdatedProbes
        inputDistribution queryDistribution := by
    unfold GoodCost BadCost at hgood
    push Not at hgood
    exact hgood.2
  have hrpow : Real.rpow p
      (4 * dataStructure.expectedUpdatedProbes
        inputDistribution queryDistribution) ≤
      Real.rpow p (dataStructure.updatedProbeCount pair.1 pair.2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_ge hp hpone
    simpa [jointUpdatedCost] using hupdated
  calc
    Real.rpow p
        (4 * dataStructure.expectedUpdatedProbes
          inputDistribution queryDistribution) ≤
        Real.rpow p (dataStructure.updatedProbeCount pair.1 pair.2 : ℝ) := hrpow
    _ = p ^ dataStructure.updatedProbeCount pair.1 pair.2 :=
      Real.rpow_natCast p _
    _ ≤ eventMass
        (maskDistribution (CellProbe.Address wordBits) p hp.le hpone)
        (fun mask ↦ Includes mask
          (probedUpdatedAddresses dataStructure pair.1 pair.2)) :=
      pow_updatedProbeCount_le_eventMass_includes dataStructure pair.1 pair.2
        p hp.le hpone

def jointGoodSamplingMass
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1) : ℝ :=
  ∑ pair : Input × Query,
    (productDistribution Input Query inputDistribution queryDistribution).mass pair *
      eventMass
        (maskDistribution (CellProbe.Address wordBits) p hp hpone)
        (fun mask ↦ Includes mask
          (probedUpdatedAddresses dataStructure pair.1 pair.2)) *
      (if GoodCost dataStructure inputDistribution queryDistribution pair then 1 else 0)

theorem half_rpow_expectedUpdated_le_jointGoodSamplingMass
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 < p) (hpone : p ≤ 1) :
    (1 / 2 : ℝ) * Real.rpow p
        (4 * dataStructure.expectedUpdatedProbes
          inputDistribution queryDistribution) ≤
      jointGoodSamplingMass dataStructure inputDistribution queryDistribution
        p hp.le hpone := by
  let distribution :=
    productDistribution Input Query inputDistribution queryDistribution
  let good := GoodCost dataStructure inputDistribution queryDistribution
  let success : Input × Query → ℝ := fun pair ↦
    eventMass
      (maskDistribution (CellProbe.Address wordBits) p hp.le hpone)
      (fun mask ↦ Includes mask
        (probedUpdatedAddresses dataStructure pair.1 pair.2))
  let baseline : ℝ := Real.rpow p
    (4 * dataStructure.expectedUpdatedProbes inputDistribution queryDistribution)
  have hbaseline : 0 ≤ baseline := Real.rpow_nonneg hp.le _
  have hgoodMass : (1 / 2 : ℝ) ≤ eventMass distribution good :=
    goodCost_eventMass_ge_half dataStructure inputDistribution queryDistribution
  calc
    (1 / 2 : ℝ) * baseline ≤
        eventMass distribution good * baseline := by
      exact mul_le_mul_of_nonneg_right hgoodMass hbaseline
    _ = ∑ pair : Input × Query,
          distribution.mass pair * baseline *
            (if good pair then 1 else 0) := by
      unfold eventMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro pair _hpair
      ring
    _ ≤ ∑ pair : Input × Query,
          distribution.mass pair * success pair *
            (if good pair then 1 else 0) := by
      apply Finset.sum_le_sum
      intro pair _hpair
      by_cases hgood : good pair
      · simp only [hgood, if_true, mul_one]
        apply mul_le_mul_of_nonneg_left _ (distribution.mass_nonnegative pair)
        exact rpow_expectedUpdated_le_maskSuccess_of_good dataStructure
          inputDistribution queryDistribution pair p hp hpone (by
            simpa [good] using hgood)
      · simp [hgood]
    _ = jointGoodSamplingMass dataStructure inputDistribution queryDistribution
          p hp.le hpone := rfl

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuGoodSampling
