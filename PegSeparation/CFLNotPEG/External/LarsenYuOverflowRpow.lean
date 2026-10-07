import PegSeparation.CFLNotPEG.External.LarsenYuOverflow
import Mathlib.Analysis.Complex.ExponentialBounds


namespace PegSeparation.External.LarsenYuOverflowRpow

noncomputable section

open LarsenYuBernoulli LarsenYuBernoulliEvents LarsenYuBernoulliTail
  LarsenYuOverflow

theorem two_mul_exp_chernoff_le_quarter_rpow
    (x : ℝ) (hx : 4 ≤ x) :
    2 * Real.exp (-(2 * Real.log 2 - 1) * x) ≤
      Real.rpow 2 (-(1 / 4 : ℝ) * x) := by
  have hlog : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have hnumeric := Real.log_two_gt_d9
    norm_num at hnumeric ⊢
    linarith
  let coefficient : ℝ := (7 / 4 : ℝ) * Real.log 2 - 1
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    nlinarith
  have hbase : Real.log 2 ≤ 4 * coefficient := by
    dsimp only [coefficient]
    nlinarith
  have hscale : 4 * coefficient ≤ x * coefficient :=
    mul_le_mul_of_nonneg_right hx hcoefficient
  have hexponent :
      Real.log 2 + (-(2 * Real.log 2 - 1) * x) ≤
        Real.log 2 * (-(1 / 4 : ℝ) * x) := by
    dsimp only [coefficient] at hscale hbase
    nlinarith
  have htwo : (2 : ℝ) = Real.exp (Real.log 2) := by
    symm
    exact Real.exp_log (by norm_num)
  have hrpow :
      Real.rpow 2 (-(1 / 4 : ℝ) * x) =
        Real.exp (Real.log 2 * (-(1 / 4 : ℝ) * x)) :=
    Real.rpow_def_of_pos (by norm_num) _
  calc
    2 * Real.exp (-(2 * Real.log 2 - 1) * x) =
        Real.exp (Real.log 2) *
          Real.exp (-(2 * Real.log 2 - 1) * x) :=
      congrArg (fun y : ℝ ↦
        y * Real.exp (-(2 * Real.log 2 - 1) * x)) htwo
    _ = Real.exp
        (Real.log 2 + (-(2 * Real.log 2 - 1) * x)) :=
      (Real.exp_add _ _).symm
    _ ≤ Real.exp (Real.log 2 * (-(1 / 4 : ℝ) * x)) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.rpow 2 (-(1 / 4 : ℝ) * x) := hrpow.symm

theorem eventMass_two_sample_overflow_le_quarter_rpow
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (cap : Nat) (first second : Finset Coordinate)
    (hfirst : first.card ≤ cap) (hsecond : second.card ≤ cap)
    (hlarge : 4 ≤ p * (cap : ℝ)) :
    eventMass (maskDistribution Coordinate p hp hpone)
        (fun selected ↦
          2 * p * (cap : ℝ) ≤ (selectedCount selected first : ℝ) ∨
          2 * p * (cap : ℝ) ≤ (selectedCount selected second : ℝ)) ≤
      Real.rpow 2 (-(1 / 4 : ℝ) * p * cap) := by
  calc
    _ ≤ 2 * Real.exp (-(2 * Real.log 2 - 1) * p * cap) :=
      eventMass_two_sample_overflow_le
        p hp hpone cap first second hfirst hsecond
    _ ≤ Real.rpow 2 (-(1 / 4 : ℝ) * (p * cap)) := by
      simpa only [mul_assoc] using
        (two_mul_exp_chernoff_le_quarter_rpow
          (p * (cap : ℝ)) hlarge)
    _ = Real.rpow 2 (-(1 / 4 : ℝ) * p * cap) := by ring_nf

end

end PegSeparation.External.LarsenYuOverflowRpow
