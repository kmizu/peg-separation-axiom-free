import PegSeparation.CFLNotPEG.External.LarsenYuFiniteMarkov


open scoped BigOperators

namespace PegSeparation.External.LarsenYuBernoulliTail

noncomputable section

open LarsenYuBernoulli LarsenYuBernoulliEvents LarsenYuFiniteMarkov

def selectedCount {Coordinate : Type} [DecidableEq Coordinate]
    (selected : Mask Coordinate) (coordinates : Finset Coordinate) : Nat :=
  (coordinates.filter fun coordinate ↦ selected coordinate = true).card

local instance selectedCountThresholdDecidable
    {Coordinate : Type} [DecidableEq Coordinate]
    (p : ℝ) (coordinates : Finset Coordinate) :
    DecidablePred (fun selected : Mask Coordinate ↦
      2 * p * (coordinates.card : ℝ) ≤ (selectedCount selected coordinates : ℝ)) :=
  fun _ ↦ Classical.propDecidable _

theorem maskMass_mul_two_pow_selectedCount
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (p : ℝ) (coordinates : Finset Coordinate) (selected : Mask Coordinate) :
    maskMass p selected * (2 : ℝ) ^ selectedCount selected coordinates =
      ∏ coordinate : Coordinate,
        if coordinate ∈ coordinates then
          (if selected coordinate then 2 * p else 1 - p)
        else
          (if selected coordinate then p else 1 - p) := by
  classical
  unfold maskMass selectedCount
  have htwo : (2 : ℝ) ^
      (coordinates.filter fun coordinate ↦ selected coordinate = true).card =
      ∏ coordinate : Coordinate,
        if coordinate ∈ coordinates.filter
            (fun coordinate ↦ selected coordinate = true) then 2 else 1 := by
    rw [Fintype.prod_ite_mem]
    simp
  rw [htwo, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro coordinate _hcoordinate
  by_cases hmem : coordinate ∈ coordinates
  · cases hselected : selected coordinate <;> simp [hmem, hselected, mul_comm]
  · cases hselected : selected coordinate <;> simp [hmem, hselected, mul_comm]

theorem expectation_two_pow_selectedCount
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (coordinates : Finset Coordinate) :
    expectation (maskDistribution Coordinate p hp hpone)
        (fun selected ↦ (2 : ℝ) ^ selectedCount selected coordinates) =
      (1 + p) ^ coordinates.card := by
  classical
  unfold expectation
  simp_rw [maskDistribution_mass,
    maskMass_mul_two_pow_selectedCount p coordinates]
  rw [← Fintype.prod_sum (fun (coordinate : Coordinate) (bit : Bool) ↦
    if coordinate ∈ coordinates then
      (if bit = true then 2 * p else 1 - p)
    else
      (if bit = true then p else 1 - p))]
  simp_rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_true, if_false, ite_self]
  change (∏ coordinate : Coordinate,
      ((if coordinate ∈ coordinates then 2 * p else p) + (1 - p))) =
    (1 + p) ^ coordinates.card
  calc
    (∏ coordinate : Coordinate,
        ((if coordinate ∈ coordinates then 2 * p else p) + (1 - p))) =
        ∏ coordinate : Coordinate,
          if coordinate ∈ coordinates then 1 + p else 1 := by
      apply Finset.prod_congr rfl
      intro coordinate _hcoordinate
      by_cases hmem : coordinate ∈ coordinates
      · simp [hmem]
        ring
      · simp [hmem]
    _ = (1 + p) ^ coordinates.card := by
      rw [Fintype.prod_ite_mem]
      simp

theorem eventMass_cost_ge_le_expectation_div
    {Outcome : Type} [Fintype Outcome]
    (distribution : FiniteDistribution Outcome) (cost : Outcome → ℝ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hcost : ∀ outcome, 0 ≤ cost outcome) :
    eventMass distribution (fun outcome ↦ threshold ≤ cost outcome) ≤
      expectation distribution cost / threshold := by
  classical
  unfold eventMass expectation
  calc
    (∑ outcome, distribution.mass outcome *
        if threshold ≤ cost outcome then 1 else 0) ≤
        ∑ outcome, distribution.mass outcome * cost outcome / threshold := by
      apply Finset.sum_le_sum
      intro outcome _houtcome
      by_cases hlarge : threshold ≤ cost outcome
      · simp only [hlarge, if_true, mul_one]
        rw [le_div_iff₀ hthreshold]
        exact mul_le_mul_of_nonneg_left hlarge
          (distribution.mass_nonnegative outcome)
      · simp only [hlarge, if_false, mul_zero]
        exact div_nonneg
          (mul_nonneg (distribution.mass_nonnegative outcome) (hcost outcome))
          hthreshold.le
    _ = (∑ outcome, distribution.mass outcome * cost outcome) / threshold := by
      rw [Finset.sum_div]

theorem eventMass_two_mul_mean_le_selectedCount_le
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (coordinates : Finset Coordinate) :
    eventMass (maskDistribution Coordinate p hp hpone)
        (fun selected ↦
          2 * p * (coordinates.card : ℝ) ≤
            (selectedCount selected coordinates : ℝ)) ≤
      Real.exp (-(2 * Real.log 2 - 1) * p * coordinates.card) := by
  classical
  let threshold : ℝ := Real.rpow 2 (2 * p * (coordinates.card : ℝ))
  let cost : Mask Coordinate → ℝ := fun selected ↦
    (2 : ℝ) ^ selectedCount selected coordinates
  have hthreshold : 0 < threshold := Real.rpow_pos_of_pos (by norm_num) _
  have hsubset : eventMass (maskDistribution Coordinate p hp hpone)
      (fun selected ↦
        2 * p * (coordinates.card : ℝ) ≤
          (selectedCount selected coordinates : ℝ)) ≤
      eventMass (maskDistribution Coordinate p hp hpone)
        (fun selected ↦ threshold ≤ cost selected) := by
    unfold eventMass
    apply Finset.sum_le_sum
    intro selected _hselected
    by_cases hlarge :
        2 * p * (coordinates.card : ℝ) ≤
          (selectedCount selected coordinates : ℝ)
    · have hpow : threshold ≤ cost selected := by
        dsimp only [threshold, cost]
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hlarge
      simp [hlarge, hpow]
    · have hmass :=
        (maskDistribution Coordinate p hp hpone).mass_nonnegative selected
      by_cases hpow : threshold ≤ cost selected
      · simp only [hlarge, if_false, mul_zero, hpow, if_true, mul_one]
        exact hmass
      · simp [hlarge, hpow]
  calc
    eventMass (maskDistribution Coordinate p hp hpone)
        (fun selected ↦
          2 * p * (coordinates.card : ℝ) ≤
            (selectedCount selected coordinates : ℝ)) ≤
        eventMass (maskDistribution Coordinate p hp hpone)
          (fun selected ↦ threshold ≤ cost selected) := hsubset
    _ ≤ expectation (maskDistribution Coordinate p hp hpone) cost / threshold :=
      eventMass_cost_ge_le_expectation_div _ _ _ hthreshold
        (fun selected ↦ by dsimp only [cost]; positivity)
    _ = (1 + p) ^ coordinates.card / threshold := by
      rw [expectation_two_pow_selectedCount]
    _ ≤ Real.exp (p * coordinates.card) / threshold := by
      apply div_le_div_of_nonneg_right _ hthreshold.le
      calc
        (1 + p) ^ coordinates.card ≤
            (Real.exp p) ^ coordinates.card := by
          exact pow_le_pow_left₀ (by linarith)
            (by simpa [add_comm] using (Real.add_one_le_exp p))
            coordinates.card
        _ = Real.exp (p * coordinates.card) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
    _ = Real.exp (-(2 * Real.log 2 - 1) * p * coordinates.card) := by
      dsimp only [threshold]
      have hpowdef :
          Real.rpow 2 (2 * p * (coordinates.card : ℝ)) =
            Real.exp (Real.log 2 * (2 * p * (coordinates.card : ℝ))) :=
        Real.rpow_def_of_pos (by norm_num) _
      rw [hpowdef]
      rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring

end

end PegSeparation.External.LarsenYuBernoulliTail
