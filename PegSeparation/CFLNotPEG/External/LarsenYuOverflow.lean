import PegSeparation.CFLNotPEG.External.LarsenYuBernoulliTail


open scoped BigOperators

namespace PegSeparation.External.LarsenYuOverflow

noncomputable section

open LarsenYuBernoulli LarsenYuBernoulliEvents LarsenYuFiniteMarkov
  LarsenYuBernoulliTail

local instance selectedCountCapThresholdDecidable
    {Coordinate : Type} [DecidableEq Coordinate]
    (p : ℝ) (cap : Nat) (coordinates : Finset Coordinate) :
    DecidablePred (fun selected : Mask Coordinate ↦
      2 * p * (cap : ℝ) ≤ (selectedCount selected coordinates : ℝ)) :=
  fun _ ↦ Classical.propDecidable _

theorem eventMass_two_mul_cap_le_selectedCount_le
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (cap : Nat) (coordinates : Finset Coordinate)
    (hcard : coordinates.card ≤ cap) :
    eventMass (maskDistribution Coordinate p hp hpone)
        (fun selected ↦
          2 * p * (cap : ℝ) ≤
            (selectedCount selected coordinates : ℝ)) ≤
      Real.exp (-(2 * Real.log 2 - 1) * p * cap) := by
  classical
  let threshold : ℝ := Real.rpow 2 (2 * p * (cap : ℝ))
  let cost : Mask Coordinate → ℝ := fun selected ↦
    (2 : ℝ) ^ selectedCount selected coordinates
  have hthreshold : 0 < threshold := Real.rpow_pos_of_pos (by norm_num) _
  have hsubset : eventMass (maskDistribution Coordinate p hp hpone)
      (fun selected ↦
        2 * p * (cap : ℝ) ≤
          (selectedCount selected coordinates : ℝ)) ≤
      eventMass (maskDistribution Coordinate p hp hpone)
        (fun selected ↦ threshold ≤ cost selected) := by
    unfold eventMass
    apply Finset.sum_le_sum
    intro selected _hselected
    by_cases hlarge :
        2 * p * (cap : ℝ) ≤
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
  have hmoment :
      expectation (maskDistribution Coordinate p hp hpone) cost ≤
        Real.exp (p * cap) := by
    rw [show expectation (maskDistribution Coordinate p hp hpone) cost =
        (1 + p) ^ coordinates.card by
      exact expectation_two_pow_selectedCount p hp hpone coordinates]
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
      _ ≤ Real.exp (p * cap) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hp
  calc
    eventMass (maskDistribution Coordinate p hp hpone)
        (fun selected ↦
          2 * p * (cap : ℝ) ≤
            (selectedCount selected coordinates : ℝ)) ≤
        eventMass (maskDistribution Coordinate p hp hpone)
          (fun selected ↦ threshold ≤ cost selected) := hsubset
    _ ≤ expectation (maskDistribution Coordinate p hp hpone) cost / threshold :=
      eventMass_cost_ge_le_expectation_div _ _ _ hthreshold
        (fun selected ↦ by dsimp only [cost]; positivity)
    _ ≤ Real.exp (p * cap) / threshold :=
      div_le_div_of_nonneg_right hmoment hthreshold.le
    _ = Real.exp (-(2 * Real.log 2 - 1) * p * cap) := by
      dsimp only [threshold]
      have hpowdef :
          Real.rpow 2 (2 * p * (cap : ℝ)) =
            Real.exp (Real.log 2 * (2 * p * (cap : ℝ))) :=
        Real.rpow_def_of_pos (by norm_num) _
      rw [hpowdef]
      rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring

theorem eventMass_two_sample_overflow_le
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (cap : Nat) (first second : Finset Coordinate)
    (hfirst : first.card ≤ cap) (hsecond : second.card ≤ cap) :
    eventMass (maskDistribution Coordinate p hp hpone)
        (fun selected ↦
          2 * p * (cap : ℝ) ≤ (selectedCount selected first : ℝ) ∨
          2 * p * (cap : ℝ) ≤ (selectedCount selected second : ℝ)) ≤
      2 * Real.exp (-(2 * Real.log 2 - 1) * p * cap) := by
  calc
    _ ≤ eventMass (maskDistribution Coordinate p hp hpone)
          (fun selected ↦
            2 * p * (cap : ℝ) ≤ (selectedCount selected first : ℝ)) +
        eventMass (maskDistribution Coordinate p hp hpone)
          (fun selected ↦
            2 * p * (cap : ℝ) ≤ (selectedCount selected second : ℝ)) :=
      eventMass_or_le_add _ _ _
    _ ≤ Real.exp (-(2 * Real.log 2 - 1) * p * cap) +
        Real.exp (-(2 * Real.log 2 - 1) * p * cap) :=
      add_le_add
        (eventMass_two_mul_cap_le_selectedCount_le
          p hp hpone cap first hfirst)
        (eventMass_two_mul_cap_le_selectedCount_le
          p hp hpone cap second hsecond)
    _ = 2 * Real.exp (-(2 * Real.log 2 - 1) * p * cap) := by ring

end

end PegSeparation.External.LarsenYuOverflow
