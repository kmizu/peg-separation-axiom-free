import PegSeparation.CFLNotPEG.External.PeakToAverage
import Mathlib.RingTheory.Polynomial.Chebyshev


open scoped BigOperators

namespace PegSeparation.External.PeakToAveragePolynomialBounds

open Polynomial

noncomputable section

def weightedCoefficientL1 (polynomial : ℝ[X]) (scale : ℝ) : ℝ :=
  polynomial.sum fun degree coefficient ↦ |coefficient| * scale ^ degree

@[simp]
theorem weightedCoefficientL1_zero (scale : ℝ) :
    weightedCoefficientL1 0 scale = 0 := by
  simp [weightedCoefficientL1]

theorem weightedCoefficientL1_nonneg (polynomial : ℝ[X]) {scale : ℝ}
    (hscale : 0 ≤ scale) :
    0 ≤ weightedCoefficientL1 polynomial scale := by
  unfold weightedCoefficientL1 Polynomial.sum
  exact Finset.sum_nonneg fun degree _ ↦
    mul_nonneg (abs_nonneg _) (pow_nonneg hscale degree)

@[simp]
theorem weightedCoefficientL1_C (coefficient scale : ℝ) :
    weightedCoefficientL1 (Polynomial.C coefficient) scale = |coefficient| := by
  simp [weightedCoefficientL1]

@[simp]
theorem weightedCoefficientL1_one (scale : ℝ) :
    weightedCoefficientL1 (1 : ℝ[X]) scale = 1 := by
  rw [show (1 : ℝ[X]) = Polynomial.C 1 by simp, weightedCoefficientL1_C]
  norm_num


@[simp]
theorem weightedCoefficientL1_X (scale : ℝ) :
    weightedCoefficientL1 (Polynomial.X : ℝ[X]) scale = scale := by
  simp [weightedCoefficientL1]

theorem weightedCoefficientL1_add_le (first second : ℝ[X]) {scale : ℝ}
    (hscale : 0 ≤ scale) :
    weightedCoefficientL1 (first + second) scale ≤
      weightedCoefficientL1 first scale + weightedCoefficientL1 second scale := by
  let commonSupport : Finset ℕ := first.support ∪ second.support
  have haddSupport : (first + second).support ⊆ commonSupport := by
    exact Polynomial.support_add.trans (by rfl)
  rw [weightedCoefficientL1,
    Polynomial.sum_eq_of_subset _ (fun _ ↦ by simp) haddSupport]
  rw [weightedCoefficientL1,
    Polynomial.sum_eq_of_subset _ (fun _ ↦ by simp)
      (Finset.subset_union_left : first.support ⊆ commonSupport)]
  rw [weightedCoefficientL1,
    Polynomial.sum_eq_of_subset _ (fun _ ↦ by simp)
      (Finset.subset_union_right : second.support ⊆ commonSupport)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro degree _
  rw [Polynomial.coeff_add]
  calc
    |first.coeff degree + second.coeff degree| * scale ^ degree ≤
        (|first.coeff degree| + |second.coeff degree|) * scale ^ degree :=
      mul_le_mul_of_nonneg_right (abs_add_le _ _) (pow_nonneg hscale _)
    _ = |first.coeff degree| * scale ^ degree +
        |second.coeff degree| * scale ^ degree := by ring

theorem weightedCoefficientL1_sub_le (first second : ℝ[X]) {scale : ℝ}
    (hscale : 0 ≤ scale) :
    weightedCoefficientL1 (first - second) scale ≤
      weightedCoefficientL1 first scale + weightedCoefficientL1 second scale := by
  let commonSupport : Finset ℕ := first.support ∪ second.support
  have hsubSupport : (first - second).support ⊆ commonSupport := by
    intro degree hdegree
    by_contra hnot
    have hfirst : first.coeff degree = 0 := by
      simpa [Polynomial.mem_support_iff, commonSupport] using
        (show degree ∉ first.support from fun h ↦ hnot (Finset.mem_union_left _ h))
    have hsecond : second.coeff degree = 0 := by
      simpa [Polynomial.mem_support_iff, commonSupport] using
        (show degree ∉ second.support from fun h ↦ hnot (Finset.mem_union_right _ h))
    rw [Polynomial.mem_support_iff, Polynomial.coeff_sub, hfirst, hsecond, sub_zero] at hdegree
    exact hdegree rfl
  rw [weightedCoefficientL1,
    Polynomial.sum_eq_of_subset _ (fun _ ↦ by simp) hsubSupport]
  rw [weightedCoefficientL1,
    Polynomial.sum_eq_of_subset _ (fun _ ↦ by simp)
      (Finset.subset_union_left : first.support ⊆ commonSupport)]
  rw [weightedCoefficientL1,
    Polynomial.sum_eq_of_subset _ (fun _ ↦ by simp)
      (Finset.subset_union_right : second.support ⊆ commonSupport)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro degree _
  rw [Polynomial.coeff_sub]
  calc
    |first.coeff degree - second.coeff degree| * scale ^ degree ≤
        (|first.coeff degree| + |second.coeff degree|) * scale ^ degree :=
      mul_le_mul_of_nonneg_right (abs_sub _ _) (pow_nonneg hscale _)
    _ = |first.coeff degree| * scale ^ degree +
        |second.coeff degree| * scale ^ degree := by ring

theorem weightedCoefficientL1_X_mul (polynomial : ℝ[X]) (scale : ℝ) :
    weightedCoefficientL1 (Polynomial.X * polynomial) scale =
      scale * weightedCoefficientL1 polynomial scale := by
  by_cases hzero : polynomial = 0
  · simp [hzero]
  rw [weightedCoefficientL1,
    Polynomial.sum_over_range (Polynomial.X * polynomial) (fun _ ↦ by simp),
    Polynomial.natDegree_X_mul hzero, Finset.sum_range_succ']
  rw [weightedCoefficientL1,
    Polynomial.sum_over_range polynomial (fun _ ↦ by simp)]
  simp only [Polynomial.coeff_X_mul, Polynomial.coeff_X_mul_zero, abs_zero,
    zero_mul, add_zero, pow_succ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro degree _
  ring

theorem weightedCoefficientL1_smul (coefficient : ℝ)
    (polynomial : ℝ[X]) (scale : ℝ) :
    weightedCoefficientL1 (coefficient • polynomial) scale =
      |coefficient| * weightedCoefficientL1 polynomial scale := by
  rw [weightedCoefficientL1,
    Polynomial.sum_smul_index polynomial coefficient]
  · simp only [abs_mul]
    simpa [weightedCoefficientL1, smul_eq_mul, mul_assoc] using
      (Polynomial.smul_sum polynomial |coefficient|
        (fun degree value ↦
          |value| * scale ^ degree)).symm
  · intro degree
    simp

theorem weightedCoefficientL1_finset_sum_le
    {ι : Type*} (indices : Finset ι) (polynomial : ι → ℝ[X])
    {scale : ℝ} (hscale : 0 ≤ scale) :
    weightedCoefficientL1 (∑ index ∈ indices, polynomial index) scale ≤
      ∑ index ∈ indices, weightedCoefficientL1 (polynomial index) scale := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hnotMember inductionHypothesis =>
      rw [Finset.sum_insert hnotMember, Finset.sum_insert hnotMember]
      exact (weightedCoefficientL1_add_le _ _ hscale).trans
        (add_le_add (le_refl _) inductionHypothesis)

@[simp]
theorem weightedCoefficientL1_monomial
    (degree : ℕ) (coefficient scale : ℝ) :
    weightedCoefficientL1 (Polynomial.monomial degree coefficient) scale =
      |coefficient| * scale ^ degree := by
  by_cases hcoefficient : coefficient = 0
  · simp [hcoefficient]
  rw [weightedCoefficientL1, Polynomial.sum_monomial_index]
  simp

theorem weightedCoefficientL1_mul_le
    (first second : ℝ[X]) {scale : ℝ} (hscale : 0 ≤ scale) :
    weightedCoefficientL1 (first * second) scale ≤
      weightedCoefficientL1 first scale * weightedCoefficientL1 second scale := by
  rw [Polynomial.mul_eq_sum_sum]
  calc
    weightedCoefficientL1
        (∑ firstDegree ∈ first.support,
          second.sum fun secondDegree coefficient ↦
            Polynomial.monomial (firstDegree + secondDegree)
              (first.coeff firstDegree * coefficient)) scale ≤
      ∑ firstDegree ∈ first.support,
        weightedCoefficientL1
          (second.sum fun secondDegree coefficient ↦
            Polynomial.monomial (firstDegree + secondDegree)
              (first.coeff firstDegree * coefficient)) scale :=
        weightedCoefficientL1_finset_sum_le first.support _ hscale
    _ ≤ ∑ firstDegree ∈ first.support,
        ∑ secondDegree ∈ second.support,
          weightedCoefficientL1
            (Polynomial.monomial (firstDegree + secondDegree)
              (first.coeff firstDegree * second.coeff secondDegree)) scale := by
      apply Finset.sum_le_sum
      intro firstDegree hfirstDegree
      rw [Polynomial.sum_def]
      exact weightedCoefficientL1_finset_sum_le second.support _ hscale
    _ = weightedCoefficientL1 first scale *
        weightedCoefficientL1 second scale := by
      symm
      rw [weightedCoefficientL1, weightedCoefficientL1,
        Polynomial.sum_def, Polynomial.sum_def, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro firstDegree hfirstDegree
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro secondDegree hsecondDegree
      rw [weightedCoefficientL1_monomial, abs_mul, pow_add]
      ring

theorem weightedCoefficientL1_C_mul
    (coefficient : ℝ) (polynomial : ℝ[X]) (scale : ℝ) :
    weightedCoefficientL1 (Polynomial.C coefficient * polynomial) scale =
      |coefficient| * weightedCoefficientL1 polynomial scale := by
  rw [← Polynomial.smul_eq_C_mul]
  exact weightedCoefficientL1_smul coefficient polynomial scale

theorem weightedCoefficientL1_pow_le
    (polynomial : ℝ[X]) (degree : ℕ) {scale : ℝ}
    (hscale : 0 ≤ scale) :
    weightedCoefficientL1 (polynomial ^ degree) scale ≤
      weightedCoefficientL1 polynomial scale ^ degree := by
  induction degree with
  | zero => simp
  | succ degree inductionHypothesis =>
      rw [pow_succ, pow_succ]
      exact (weightedCoefficientL1_mul_le _ _ hscale).trans
        (mul_le_mul_of_nonneg_right inductionHypothesis
          (weightedCoefficientL1_nonneg polynomial hscale))

theorem weightedCoefficientL1_comp_le
    (outer inner : ℝ[X]) {scale : ℝ} (hscale : 0 ≤ scale) :
    weightedCoefficientL1 (outer.comp inner) scale ≤
      weightedCoefficientL1 outer
        (weightedCoefficientL1 inner scale) := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def]
  calc
    weightedCoefficientL1
        (∑ degree ∈ outer.support,
          Polynomial.C (outer.coeff degree) * inner ^ degree) scale ≤
      ∑ degree ∈ outer.support,
        weightedCoefficientL1
          (Polynomial.C (outer.coeff degree) * inner ^ degree) scale :=
        weightedCoefficientL1_finset_sum_le outer.support _ hscale
    _ ≤ ∑ degree ∈ outer.support,
        |outer.coeff degree| *
          weightedCoefficientL1 inner scale ^ degree := by
      apply Finset.sum_le_sum
      intro degree hdegree
      rw [weightedCoefficientL1_C_mul]
      exact mul_le_mul_of_nonneg_left
        (weightedCoefficientL1_pow_le inner degree hscale) (abs_nonneg _)
    _ = weightedCoefficientL1 outer
        (weightedCoefficientL1 inner scale) := by
      simp only [weightedCoefficientL1, Polynomial.sum_def]

theorem weightedCoefficientL1_two_mul_X_mul
    (polynomial : ℝ[X]) (scale : ℝ) :
    weightedCoefficientL1 ((2 : ℝ[X]) * Polynomial.X * polynomial) scale =
      2 * scale * weightedCoefficientL1 polynomial scale := by
  calc
    weightedCoefficientL1 ((2 : ℝ[X]) * Polynomial.X * polynomial) scale =
        weightedCoefficientL1 ((2 : ℝ) • (Polynomial.X * polynomial)) scale := by
      congr 1
      rw [Polynomial.smul_eq_C_mul, Polynomial.C_ofNat, mul_assoc]
    _ = |(2 : ℝ)| * weightedCoefficientL1
        (Polynomial.X * polynomial) scale :=
      weightedCoefficientL1_smul 2 (Polynomial.X * polynomial) scale
    _ = 2 * scale * weightedCoefficientL1 polynomial scale := by
      rw [weightedCoefficientL1_X_mul]
      ring

theorem weightedCoefficientL1_chebyshevT_le
    (degree : ℕ) {scale : ℝ} (hscale : 0 ≤ scale) :
    weightedCoefficientL1
        (Polynomial.Chebyshev.T ℝ (degree : ℤ)) scale ≤
      (2 * scale + 1) ^ degree := by
  induction degree using Nat.twoStepInduction with
  | zero =>
      change weightedCoefficientL1 (Polynomial.Chebyshev.T ℝ 0) scale ≤ 1
      rw [Polynomial.Chebyshev.T_zero]
      rw [show (1 : ℝ[X]) = Polynomial.C 1 by simp,
        weightedCoefficientL1_C]
      norm_num
  | one =>
      norm_num [Polynomial.Chebyshev.T_one, weightedCoefficientL1]
      linarith
  | more degree hdegree hdegreeSucc =>
      rw [show ((degree + 2 : ℕ) : ℤ) = (degree : ℤ) + 2 by omega]
      rw [Polynomial.Chebyshev.T_add_two]
      calc
        weightedCoefficientL1
            (2 * Polynomial.X * Polynomial.Chebyshev.T ℝ ((degree : ℤ) + 1) -
              Polynomial.Chebyshev.T ℝ (degree : ℤ)) scale ≤
          weightedCoefficientL1
              (2 * Polynomial.X * Polynomial.Chebyshev.T ℝ ((degree : ℤ) + 1)) scale +
            weightedCoefficientL1
              (Polynomial.Chebyshev.T ℝ (degree : ℤ)) scale :=
          weightedCoefficientL1_sub_le _ _ hscale
        _ = 2 * scale * weightedCoefficientL1
              (Polynomial.Chebyshev.T ℝ ((degree : ℤ) + 1)) scale +
            weightedCoefficientL1
              (Polynomial.Chebyshev.T ℝ (degree : ℤ)) scale := by
          rw [weightedCoefficientL1_two_mul_X_mul]
        _ ≤ 2 * scale * (2 * scale + 1) ^ (degree + 1) +
            (2 * scale + 1) ^ degree := by
          have hfactor : 0 ≤ 2 * scale := by positivity
          exact add_le_add
            (mul_le_mul_of_nonneg_left (by simpa using hdegreeSucc) hfactor)
            hdegree
        _ ≤ (2 * scale + 1) ^ (degree + 2) := by
          have hbase : 0 ≤ 2 * scale + 1 := by linarith
          have hpow : 0 ≤ (2 * scale + 1) ^ degree := pow_nonneg hbase degree
          calc
            2 * scale * (2 * scale + 1) ^ (degree + 1) +
                (2 * scale + 1) ^ degree =
              (2 * scale * (2 * scale + 1) + 1) *
                (2 * scale + 1) ^ degree := by ring
            _ ≤ (2 * scale + 1) ^ 2 * (2 * scale + 1) ^ degree := by
              apply mul_le_mul_of_nonneg_right _ hpow
              nlinarith
            _ = (2 * scale + 1) ^ (degree + 2) := by ring

end

end PegSeparation.External.PeakToAveragePolynomialBounds
