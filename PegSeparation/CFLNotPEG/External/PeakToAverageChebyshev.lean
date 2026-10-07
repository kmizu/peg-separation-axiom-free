import PegSeparation.CFLNotPEG.External.PeakToAveragePolynomialBounds
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series


open scoped BigOperators fwdDiff

namespace PegSeparation.External.PeakToAverageChebyshev

noncomputable section

open Finset Function Polynomial
open PeakToAverage


def trueCoordinates {k : Nat} (point : BoolCube k) : Finset (Fin k) :=
  Finset.univ.filter fun coordinate => point coordinate = true

@[simp] theorem trueCoordinates_zeroCube (k : Nat) :
    trueCoordinates (zeroCube k) = ∅ := by
  ext coordinate
  simp [trueCoordinates, zeroCube]

theorem trueCoordinates_eq_empty_iff {k : Nat} (point : BoolCube k) :
    trueCoordinates point = ∅ ↔ point = zeroCube k := by
  constructor
  · intro hempty
    funext coordinate
    have hfalse : point coordinate ≠ true := by
      intro htrue
      have : coordinate ∈ trueCoordinates point := by
        simp [trueCoordinates, htrue]
      simp [hempty] at this
    cases hpoint : point coordinate <;> simp_all [zeroCube]
  · rintro rfl
    exact trueCoordinates_zeroCube k

@[simp] theorem card_trueCoordinates_le {k : Nat} (point : BoolCube k) :
    (trueCoordinates point).card ≤ k := by
  have hsubset : trueCoordinates point ⊆ (Finset.univ : Finset (Fin k)) := by
    exact Finset.filter_subset _ _
  simpa using Finset.card_le_card hsubset

def newtonCoefficient {k : Nat} (q : ℝ[X])
    (coordinates : Finset (Fin k)) : ℝ :=
  ((fwdDiff (1 : ℝ))^[coordinates.card] q.eval) 0

theorem newtonCoefficient_eq_zero_of_natDegree_lt {k : Nat} (q : ℝ[X])
    (coordinates : Finset (Fin k)) (hdegree : q.natDegree < coordinates.card) :
    newtonCoefficient q coordinates = 0 := by
  have hzero := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := q) hdegree
  exact congrFun hzero 0

theorem evaluate_newtonCoefficient {k : Nat} (q : ℝ[X]) (point : BoolCube k) :
    evaluate (newtonCoefficient q) point =
      q.eval ((trueCoordinates point).card : ℝ) := by
  classical
  let support := trueCoordinates point
  have hmonomial (coordinates : Finset (Fin k)) :
      monomial coordinates point = if coordinates ⊆ support then 1 else 0 := by
    by_cases hsubset : coordinates ⊆ support
    · have hall : ∀ coordinate ∈ coordinates, point coordinate = true := by
        intro coordinate hcoordinate
        have := hsubset hcoordinate
        simpa [support, trueCoordinates] using this
      rw [PeakToAverage.monomial, if_pos hall, if_pos hsubset]
    · have hnotall : ¬ ∀ coordinate ∈ coordinates, point coordinate = true := by
        intro hall
        apply hsubset
        intro coordinate hcoordinate
        simp [support, trueCoordinates, hall coordinate hcoordinate]
      rw [PeakToAverage.monomial, if_neg hnotall, if_neg hsubset]
  calc
    evaluate (newtonCoefficient q) point =
        ∑ coordinates ∈ support.powerset, newtonCoefficient q coordinates := by
      rw [PeakToAverage.evaluate]
      simp_rw [hmonomial, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext coordinates
      simp
    _ = ∑ degree ∈ Finset.range (support.card + 1),
        support.card.choose degree •
          ((fwdDiff (1 : ℝ))^[degree] q.eval) 0 := by
      simpa [newtonCoefficient] using
        (Finset.sum_powerset_apply_card
          (x := support)
          (f := fun degree => ((fwdDiff (1 : ℝ))^[degree] q.eval) 0))
    _ = q.eval ((support.card : Nat) : ℝ) := by
      symm
      simpa using
        (shift_eq_sum_fwdDiff_iter (h := (1 : ℝ)) q.eval support.card 0)
    _ = q.eval ((trueCoordinates point).card : ℝ) := rfl


def powerDifference (power order : Nat) : ℝ :=
  ((fwdDiff (1 : ℝ))^[order] (fun x : ℝ => x ^ power)) 0

theorem powerDifference_nonnegative (power order : Nat) :
    0 ≤ powerDifference power order := by
  induction order generalizing power with
  | zero =>
      simp [powerDifference]
  | succ order ih =>
      have hfirst :
          fwdDiff (1 : ℝ) (fun x : ℝ => x ^ power) =
            ∑ exponent ∈ Finset.range power,
              power.choose exponent • (fun x : ℝ => x ^ exponent) := by
        ext x
        simp [fwdDiff, add_pow, Finset.sum_range_succ, nsmul_eq_mul, mul_comm]
      rw [powerDifference, Function.iterate_succ_apply, hfirst,
        fwdDiff_iter_finsetSum, Finset.sum_apply]
      exact Finset.sum_nonneg fun exponent _ => by
        rw [fwdDiff_iter_const_smul, Pi.smul_apply, nsmul_eq_mul]
        exact mul_nonneg (by positivity) (by simpa [powerDifference] using ih exponent)

theorem newtonCoefficient_eq_sum_coeff_mul_powerDifference
    {k : Nat} (q : ℝ[X]) (coordinates : Finset (Fin k)) :
    newtonCoefficient q coordinates =
      ∑ power ∈ Finset.range (q.natDegree + 1),
        q.coeff power * powerDifference power coordinates.card := by
  unfold newtonCoefficient powerDifference
  simp_rw [q.eval_eq_sum_range,
    ← Finset.sum_apply _ _ (fun power x => q.coeff power * x ^ power),
    ← smul_eq_mul, ← Pi.smul_def, fwdDiff_iter_finsetSum,
    fwdDiff_iter_const_smul, Finset.sum_apply, Pi.smul_apply]

theorem abs_newtonCoefficient_le
    {k : Nat} (q : ℝ[X]) (coordinates : Finset (Fin k)) :
    |newtonCoefficient q coordinates| ≤
      ∑ power ∈ Finset.range (q.natDegree + 1),
        |q.coeff power| * powerDifference power coordinates.card := by
  rw [newtonCoefficient_eq_sum_coeff_mul_powerDifference]
  calc
    |∑ power ∈ Finset.range (q.natDegree + 1),
        q.coeff power * powerDifference power coordinates.card| ≤
        ∑ power ∈ Finset.range (q.natDegree + 1),
          |q.coeff power * powerDifference power coordinates.card| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ power ∈ Finset.range (q.natDegree + 1),
        |q.coeff power| * powerDifference power coordinates.card := by
      apply Finset.sum_congr rfl
      intro power _
      rw [abs_mul, abs_of_nonneg (powerDifference_nonnegative power coordinates.card)]

theorem sum_choose_mul_powerDifference (k power : Nat) :
    (∑ order ∈ Finset.range (k + 1),
        (k.choose order : ℝ) * powerDifference power order) =
      (k : ℝ) ^ power := by
  simpa [powerDifference, nsmul_eq_mul] using
    (shift_eq_sum_fwdDiff_iter
      (h := (1 : ℝ)) (fun x : ℝ => x ^ power) k 0).symm

theorem sum_powerDifference_card (k power : Nat) :
    (∑ coordinates : Finset (Fin k),
        powerDifference power coordinates.card) = (k : ℝ) ^ power := by
  rw [show (Finset.univ : Finset (Finset (Fin k))) =
      (Finset.univ : Finset (Fin k)).powerset by
    ext coordinates
    simp]
  rw [Finset.sum_powerset_apply_card]
  simpa [nsmul_eq_mul] using sum_choose_mul_powerDifference k power

def weightedCoefficientL1 (q : ℝ[X]) (s : ℝ) : ℝ :=
  ∑ power ∈ Finset.range (q.natDegree + 1), |q.coeff power| * s ^ power

theorem weightedCoefficientL1_eq_polynomialBounds (q : ℝ[X]) (s : ℝ) :
    weightedCoefficientL1 q s =
      PeakToAveragePolynomialBounds.weightedCoefficientL1 q s := by
  rw [weightedCoefficientL1,
    PeakToAveragePolynomialBounds.weightedCoefficientL1,
    Polynomial.sum_over_range q (fun _ => by simp)]

theorem polynomialBounds_weightedCoefficientL1_prod_le
    {ι : Type*} (indices : Finset ι) (polynomial : ι → ℝ[X])
    {scale : ℝ} (hscale : 0 ≤ scale) :
    PeakToAveragePolynomialBounds.weightedCoefficientL1
        (∏ index ∈ indices, polynomial index) scale ≤
      ∏ index ∈ indices,
        PeakToAveragePolynomialBounds.weightedCoefficientL1
          (polynomial index) scale := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hnotMember inductionHypothesis =>
      rw [Finset.prod_insert hnotMember, Finset.prod_insert hnotMember]
      exact
        (PeakToAveragePolynomialBounds.weightedCoefficientL1_mul_le _ _ hscale).trans
          (mul_le_mul_of_nonneg_left inductionHypothesis
            (PeakToAveragePolynomialBounds.weightedCoefficientL1_nonneg _ hscale))

theorem sum_abs_newtonCoefficient_le_weightedCoefficientL1
    (k : Nat) (q : ℝ[X]) :
    (∑ coordinates : Finset (Fin k), |newtonCoefficient q coordinates|) ≤
      weightedCoefficientL1 q k := by
  calc
    (∑ coordinates : Finset (Fin k), |newtonCoefficient q coordinates|) ≤
        ∑ coordinates : Finset (Fin k),
          ∑ power ∈ Finset.range (q.natDegree + 1),
            |q.coeff power| * powerDifference power coordinates.card := by
      apply Finset.sum_le_sum
      intro coordinates _
      exact abs_newtonCoefficient_le q coordinates
    _ = ∑ power ∈ Finset.range (q.natDegree + 1),
          |q.coeff power| *
            ∑ coordinates : Finset (Fin k),
              powerDifference power coordinates.card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro power _
      rw [Finset.mul_sum]
    _ = weightedCoefficientL1 q k := by
      apply Finset.sum_congr rfl
      intro power _
      rw [sum_powerDifference_card]


def affineArgument (k cutoff x : ℝ) : ℝ := (x - k) / (k - cutoff)

def shiftedChebyshev (degree : Nat) (k cutoff : ℝ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ degree).comp
    ((X - C k) * C ((k - cutoff)⁻¹))

@[simp] theorem eval_shiftedChebyshev
    (degree : Nat) (k cutoff x : ℝ) :
    (shiftedChebyshev degree k cutoff).eval x =
      (Polynomial.Chebyshev.T ℝ degree).eval (affineArgument k cutoff x) := by
  simp [shiftedChebyshev, affineArgument, div_eq_mul_inv]

theorem polynomialBounds_affinePolynomial_le_four
    {k cutoff : Nat} (hcutoff : 0 < cutoff) (htwo : 2 * cutoff ≤ k) :
    PeakToAveragePolynomialBounds.weightedCoefficientL1
        (((X : ℝ[X]) - C (k : ℝ)) *
          C (((k : ℝ) - (cutoff : ℝ))⁻¹)) k ≤ 4 := by
  have hcutoffK : cutoff < k := by omega
  have hden : 0 < (k : ℝ) - (cutoff : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hcutoffK)
  have hlinear :
      PeakToAveragePolynomialBounds.weightedCoefficientL1
          ((X : ℝ[X]) - C (k : ℝ)) k ≤ 2 * (k : ℝ) := by
    calc
      PeakToAveragePolynomialBounds.weightedCoefficientL1
          ((X : ℝ[X]) - C (k : ℝ)) k ≤
          PeakToAveragePolynomialBounds.weightedCoefficientL1 (X : ℝ[X]) k +
            PeakToAveragePolynomialBounds.weightedCoefficientL1
              (C (k : ℝ)) k :=
        PeakToAveragePolynomialBounds.weightedCoefficientL1_sub_le _ _
          (Nat.cast_nonneg k)
      _ = (k : ℝ) + |(k : ℝ)| := by
        rw [PeakToAveragePolynomialBounds.weightedCoefficientL1_X,
          PeakToAveragePolynomialBounds.weightedCoefficientL1_C]
      _ = 2 * (k : ℝ) := by
        rw [abs_of_nonneg (Nat.cast_nonneg k)]
        ring
  have hconstant :
      PeakToAveragePolynomialBounds.weightedCoefficientL1
          (C (((k : ℝ) - (cutoff : ℝ))⁻¹)) k =
        ((k : ℝ) - (cutoff : ℝ))⁻¹ := by
    rw [PeakToAveragePolynomialBounds.weightedCoefficientL1_C,
      abs_of_pos (inv_pos.mpr hden)]
  calc
    PeakToAveragePolynomialBounds.weightedCoefficientL1
        (((X : ℝ[X]) - C (k : ℝ)) *
          C (((k : ℝ) - (cutoff : ℝ))⁻¹)) k ≤
        PeakToAveragePolynomialBounds.weightedCoefficientL1
            ((X : ℝ[X]) - C (k : ℝ)) k *
          PeakToAveragePolynomialBounds.weightedCoefficientL1
            (C (((k : ℝ) - (cutoff : ℝ))⁻¹)) k :=
      PeakToAveragePolynomialBounds.weightedCoefficientL1_mul_le _ _
        (Nat.cast_nonneg k)
    _ ≤ (2 * (k : ℝ)) * ((k : ℝ) - (cutoff : ℝ))⁻¹ := by
      rw [hconstant]
      exact mul_le_mul_of_nonneg_right hlinear (inv_nonneg.mpr hden.le)
    _ ≤ 4 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hden]
      have htwoReal : 2 * (cutoff : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast htwo
      nlinarith

theorem polynomialBounds_shiftedChebyshev_le_nine_pow
    {k cutoff degree : Nat}
    (hcutoff : 0 < cutoff) (htwo : 2 * cutoff ≤ k) :
    PeakToAveragePolynomialBounds.weightedCoefficientL1
        (shiftedChebyshev degree k cutoff) k ≤ (9 : ℝ) ^ degree := by
  let affinePolynomial : ℝ[X] :=
    ((X : ℝ[X]) - C (k : ℝ)) *
      C (((k : ℝ) - (cutoff : ℝ))⁻¹)
  have haffineNonnegative :
      0 ≤ PeakToAveragePolynomialBounds.weightedCoefficientL1
        affinePolynomial k :=
    PeakToAveragePolynomialBounds.weightedCoefficientL1_nonneg _
      (Nat.cast_nonneg k)
  have haffineFour :
      PeakToAveragePolynomialBounds.weightedCoefficientL1
        affinePolynomial k ≤ 4 := by
    simpa [affinePolynomial] using
      polynomialBounds_affinePolynomial_le_four hcutoff htwo
  rw [shiftedChebyshev]
  calc
    PeakToAveragePolynomialBounds.weightedCoefficientL1
        ((Polynomial.Chebyshev.T ℝ degree).comp affinePolynomial) k ≤
        PeakToAveragePolynomialBounds.weightedCoefficientL1
          (Polynomial.Chebyshev.T ℝ degree)
          (PeakToAveragePolynomialBounds.weightedCoefficientL1
            affinePolynomial k) :=
      PeakToAveragePolynomialBounds.weightedCoefficientL1_comp_le _ _
        (Nat.cast_nonneg k)
    _ ≤ (2 * PeakToAveragePolynomialBounds.weightedCoefficientL1
          affinePolynomial k + 1) ^ degree :=
      PeakToAveragePolynomialBounds.weightedCoefficientL1_chebyshevT_le
        degree haffineNonnegative
    _ ≤ (9 : ℝ) ^ degree := by
      apply pow_le_pow_left₀
      · linarith
      · linarith

abbrev mainFactor (k t mainDegree : Nat) : ℝ[X] :=
  shiftedChebyshev mainDegree k t

def correctionFactor (k i degree : Nat) : ℝ[X] :=
  (shiftedChebyshev degree k i -
      C ((Polynomial.Chebyshev.T ℝ degree).eval (-1))) * C (2⁻¹ : ℝ)

@[simp] theorem eval_correctionFactor
    (k i degree : Nat) (x : ℝ) :
    (correctionFactor k i degree).eval x =
      ((Polynomial.Chebyshev.T ℝ degree).eval
          (affineArgument k i x) -
        (Polynomial.Chebyshev.T ℝ degree).eval (-1)) / 2 := by
  simp [correctionFactor, div_eq_mul_inv]

theorem polynomialBounds_correctionFactor_le_nine_pow
    {k i degree : Nat} (hi : 0 < i) (htwo : 2 * i ≤ k) :
    PeakToAveragePolynomialBounds.weightedCoefficientL1
        (correctionFactor k i degree) k ≤ (9 : ℝ) ^ degree := by
  have hshifted :=
    polynomialBounds_shiftedChebyshev_le_nine_pow
      (k := k) (cutoff := i) (degree := degree) hi htwo
  have hminusOne :
      |(Polynomial.Chebyshev.T ℝ degree).eval (-1)| ≤ 1 := by
    apply Polynomial.Chebyshev.abs_eval_T_real_le_one
    norm_num
  have hconstant :
      PeakToAveragePolynomialBounds.weightedCoefficientL1
          (C ((Polynomial.Chebyshev.T ℝ degree).eval (-1))) k ≤ 1 := by
    rw [PeakToAveragePolynomialBounds.weightedCoefficientL1_C]
    exact hminusOne
  have hdifference :
      PeakToAveragePolynomialBounds.weightedCoefficientL1
          (shiftedChebyshev degree k i -
            C ((Polynomial.Chebyshev.T ℝ degree).eval (-1))) k ≤
        (9 : ℝ) ^ degree + 1 := by
    calc
      PeakToAveragePolynomialBounds.weightedCoefficientL1
          (shiftedChebyshev degree k i -
            C ((Polynomial.Chebyshev.T ℝ degree).eval (-1))) k ≤
          PeakToAveragePolynomialBounds.weightedCoefficientL1
              (shiftedChebyshev degree k i) k +
            PeakToAveragePolynomialBounds.weightedCoefficientL1
              (C ((Polynomial.Chebyshev.T ℝ degree).eval (-1))) k :=
        PeakToAveragePolynomialBounds.weightedCoefficientL1_sub_le _ _
          (Nat.cast_nonneg k)
      _ ≤ (9 : ℝ) ^ degree + 1 := by
        exact add_le_add hshifted hconstant
  rw [correctionFactor]
  calc
    PeakToAveragePolynomialBounds.weightedCoefficientL1
        ((shiftedChebyshev degree k i -
            C ((Polynomial.Chebyshev.T ℝ degree).eval (-1))) *
          C (2⁻¹ : ℝ)) k ≤
        PeakToAveragePolynomialBounds.weightedCoefficientL1
            (shiftedChebyshev degree k i -
              C ((Polynomial.Chebyshev.T ℝ degree).eval (-1))) k *
          PeakToAveragePolynomialBounds.weightedCoefficientL1
            (C (2⁻¹ : ℝ)) k :=
      PeakToAveragePolynomialBounds.weightedCoefficientL1_mul_le _ _
        (Nat.cast_nonneg k)
    _ = PeakToAveragePolynomialBounds.weightedCoefficientL1
          (shiftedChebyshev degree k i -
            C ((Polynomial.Chebyshev.T ℝ degree).eval (-1))) k * (1 / 2) := by
      rw [PeakToAveragePolynomialBounds.weightedCoefficientL1_C]
      norm_num
    _ ≤ ((9 : ℝ) ^ degree + 1) * (1 / 2) :=
      mul_le_mul_of_nonneg_right hdifference (by norm_num)
    _ ≤ (9 : ℝ) ^ degree := by
      have hpower : (1 : ℝ) ≤ (9 : ℝ) ^ degree :=
        one_le_pow₀ (by norm_num)
      nlinarith

def appendixPolynomial
    (k t mainDegree : Nat) (correctionDegree : Nat → Nat) : ℝ[X] :=
  mainFactor k t mainDegree *
    ∏ i ∈ Finset.Ico 1 t, correctionFactor k i (correctionDegree i)

@[simp] theorem eval_appendixPolynomial
    (k t mainDegree : Nat) (correctionDegree : Nat → Nat) (x : ℝ) :
    (appendixPolynomial k t mainDegree correctionDegree).eval x =
      (mainFactor k t mainDegree).eval x *
        ∏ i ∈ Finset.Ico 1 t,
          (correctionFactor k i (correctionDegree i)).eval x := by
  simp [appendixPolynomial, Polynomial.eval_prod]

theorem polynomialBounds_appendixPolynomial_le_nine_pow
    {k t mainDegree : Nat} (correctionDegree : Nat → Nat)
    (ht : 0 < t) (htwo : 2 * t ≤ k) :
    PeakToAveragePolynomialBounds.weightedCoefficientL1
        (appendixPolynomial k t mainDegree correctionDegree) k ≤
      (9 : ℝ) ^
        (mainDegree + ∑ i ∈ Finset.Ico 1 t, correctionDegree i) := by
  have hmain :
      PeakToAveragePolynomialBounds.weightedCoefficientL1
          (mainFactor k t mainDegree) k ≤ (9 : ℝ) ^ mainDegree := by
    exact polynomialBounds_shiftedChebyshev_le_nine_pow ht htwo
  have hcorrection :
      ∀ i ∈ Finset.Ico 1 t,
        PeakToAveragePolynomialBounds.weightedCoefficientL1
            (correctionFactor k i (correctionDegree i)) k ≤
          (9 : ℝ) ^ (correctionDegree i) := by
    intro i hi
    have hiBounds := Finset.mem_Ico.mp hi
    have hiPositive : 0 < i := hiBounds.1
    have htwoI : 2 * i ≤ k := by omega
    exact polynomialBounds_correctionFactor_le_nine_pow hiPositive htwoI
  have hproduct :
      PeakToAveragePolynomialBounds.weightedCoefficientL1
          (∏ i ∈ Finset.Ico 1 t,
            correctionFactor k i (correctionDegree i)) k ≤
        (9 : ℝ) ^ (∑ i ∈ Finset.Ico 1 t, correctionDegree i) := by
    calc
      PeakToAveragePolynomialBounds.weightedCoefficientL1
          (∏ i ∈ Finset.Ico 1 t,
            correctionFactor k i (correctionDegree i)) k ≤
          ∏ i ∈ Finset.Ico 1 t,
            PeakToAveragePolynomialBounds.weightedCoefficientL1
              (correctionFactor k i (correctionDegree i)) k :=
        polynomialBounds_weightedCoefficientL1_prod_le _ _
          (Nat.cast_nonneg k)
      _ ≤ ∏ i ∈ Finset.Ico 1 t, (9 : ℝ) ^ (correctionDegree i) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact PeakToAveragePolynomialBounds.weightedCoefficientL1_nonneg _
            (Nat.cast_nonneg k)
        · exact hcorrection
      _ = (9 : ℝ) ^ (∑ i ∈ Finset.Ico 1 t, correctionDegree i) :=
        Finset.prod_pow_eq_pow_sum _ _ _
  rw [appendixPolynomial]
  calc
    PeakToAveragePolynomialBounds.weightedCoefficientL1
        (mainFactor k t mainDegree *
          ∏ i ∈ Finset.Ico 1 t,
            correctionFactor k i (correctionDegree i)) k ≤
        PeakToAveragePolynomialBounds.weightedCoefficientL1
            (mainFactor k t mainDegree) k *
          PeakToAveragePolynomialBounds.weightedCoefficientL1
            (∏ i ∈ Finset.Ico 1 t,
              correctionFactor k i (correctionDegree i)) k :=
      PeakToAveragePolynomialBounds.weightedCoefficientL1_mul_le _ _
        (Nat.cast_nonneg k)
    _ ≤ (9 : ℝ) ^ mainDegree *
        (9 : ℝ) ^ (∑ i ∈ Finset.Ico 1 t, correctionDegree i) := by
      exact mul_le_mul hmain hproduct
        (PeakToAveragePolynomialBounds.weightedCoefficientL1_nonneg _
          (Nat.cast_nonneg k))
        (pow_nonneg (by norm_num) _)
    _ = (9 : ℝ) ^
        (mainDegree + ∑ i ∈ Finset.Ico 1 t, correctionDegree i) := by
      rw [pow_add]

theorem natDegree_shiftedChebyshev_le
    (degree : Nat) (k cutoff : ℝ) :
    (shiftedChebyshev degree k cutoff).natDegree ≤ degree := by
  have haffine :
      (((X : ℝ[X]) - C k) * C ((k - cutoff)⁻¹)).natDegree ≤ 1 := by
    calc
      (((X : ℝ[X]) - C k) * C ((k - cutoff)⁻¹)).natDegree ≤
          ((X : ℝ[X]) - C k).natDegree +
            (C ((k - cutoff)⁻¹) : ℝ[X]).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 1 := by simp
  calc
    (shiftedChebyshev degree k cutoff).natDegree ≤
        (Polynomial.Chebyshev.T ℝ degree).natDegree *
          (((X : ℝ[X]) - C k) * C ((k - cutoff)⁻¹)).natDegree := by
      exact Polynomial.natDegree_comp_le
    _ ≤ degree * 1 := Nat.mul_le_mul (by simp) haffine
    _ = degree := Nat.mul_one degree

theorem natDegree_correctionFactor_le
    (k i degree : Nat) :
    (correctionFactor k i degree).natDegree ≤ degree := by
  calc
    (correctionFactor k i degree).natDegree ≤
        (shiftedChebyshev degree k i -
          C ((Polynomial.Chebyshev.T ℝ degree).eval (-1))).natDegree +
            (C (2⁻¹ : ℝ) : ℝ[X]).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ degree + 0 := Nat.add_le_add
      ((Polynomial.natDegree_sub_le _ _).trans
        (max_le (natDegree_shiftedChebyshev_le degree k i) (by simp)))
      (by simp)
    _ = degree := Nat.add_zero degree

theorem natDegree_appendixPolynomial_le
    (k t mainDegree : Nat) (correctionDegree : Nat → Nat) :
    (appendixPolynomial k t mainDegree correctionDegree).natDegree ≤
      mainDegree + ∑ i ∈ Finset.Ico 1 t, correctionDegree i := by
  calc
    (appendixPolynomial k t mainDegree correctionDegree).natDegree ≤
        (mainFactor k t mainDegree).natDegree +
          (∏ i ∈ Finset.Ico 1 t,
            correctionFactor k i (correctionDegree i)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ mainDegree +
        ∑ i ∈ Finset.Ico 1 t,
          (correctionFactor k i (correctionDegree i)).natDegree :=
      Nat.add_le_add (natDegree_shiftedChebyshev_le mainDegree k t)
        (Polynomial.natDegree_prod_le
          (s := Finset.Ico 1 t)
          (f := fun i => correctionFactor k i (correctionDegree i)))
    _ ≤ mainDegree + ∑ i ∈ Finset.Ico 1 t, correctionDegree i := by
      gcongr with i hi
      exact natDegree_correctionFactor_le k i (correctionDegree i)

theorem abs_eval_mainFactor_le_one
    {k t : Nat} (mainDegree : Nat) (htk : t < k)
    {x : ℝ} (hxLower : (t : ℝ) ≤ x) (hxUpper : x ≤ k) :
    |(mainFactor k t mainDegree).eval x| ≤ 1 := by
  rw [eval_shiftedChebyshev]
  apply Polynomial.Chebyshev.abs_eval_T_real_le_one
  apply (abs_le).2
  have hden : 0 < (k : ℝ) - (t : ℝ) := by
    apply sub_pos.mpr
    exact_mod_cast htk
  constructor
  · rw [affineArgument, le_div_iff₀ hden]
    linarith
  · rw [affineArgument, div_le_iff₀ hden]
    linarith

theorem eval_correctionFactor_at_index
    {k i degree : Nat} (hik : i < k) :
    (correctionFactor k i degree).eval (i : ℝ) = 0 := by
  rw [eval_correctionFactor]
  have hden : (k : ℝ) - (i : ℝ) ≠ 0 := by
    have hlt : (i : ℝ) < (k : ℝ) := by exact_mod_cast hik
    linarith
  have harg : affineArgument (k : ℝ) (i : ℝ) (i : ℝ) = (-1 : ℝ) := by
    rw [affineArgument]
    field_simp
    ring
  rw [harg]
  simp

theorem abs_eval_correctionFactor_le_one
    {k i degree : Nat} (hik : i < k)
    {x : ℝ} (hxLower : (i : ℝ) ≤ x) (hxUpper : x ≤ k) :
    |(correctionFactor k i degree).eval x| ≤ 1 := by
  rw [eval_correctionFactor]
  have hden : 0 < (k : ℝ) - (i : ℝ) := by
    apply sub_pos.mpr
    exact_mod_cast hik
  have harg : |affineArgument k i x| ≤ 1 := by
    apply (abs_le).2
    constructor
    · rw [affineArgument, le_div_iff₀ hden]
      linarith
    · rw [affineArgument, div_le_iff₀ hden]
      linarith
  have hcurrent :=
    Polynomial.Chebyshev.abs_eval_T_real_le_one (degree : ℤ) harg
  have hminusOne :
      |(Polynomial.Chebyshev.T ℝ degree).eval (-1)| ≤ 1 := by
    apply Polynomial.Chebyshev.abs_eval_T_real_le_one
    norm_num
  have hsub :
      |(Polynomial.Chebyshev.T ℝ degree).eval (affineArgument k i x) -
        (Polynomial.Chebyshev.T ℝ degree).eval (-1)| ≤ 2 :=
    (abs_sub _ _).trans (by linarith)
  calc
    |((Polynomial.Chebyshev.T ℝ degree).eval (affineArgument k i x) -
        (Polynomial.Chebyshev.T ℝ degree).eval (-1)) / 2| =
        |(Polynomial.Chebyshev.T ℝ degree).eval (affineArgument k i x) -
          (Polynomial.Chebyshev.T ℝ degree).eval (-1)| / |(2 : ℝ)| := abs_div _ _
    _ ≤ 2 / |(2 : ℝ)| := by
      exact div_le_div_of_nonneg_right hsub (abs_nonneg _)
    _ = 1 := by norm_num


theorem sqrt_le_arcosh_one_add
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1) :
    Real.sqrt epsilon ≤ Real.arcosh (1 + epsilon) := by
  have hhalfNonnegative : 0 ≤ epsilon / 2 := by positivity
  have hhalfLtOne : epsilon / 2 < 1 := by linarith
  have hcoshExp :
      Real.cosh (Real.sqrt epsilon) ≤ Real.exp (epsilon / 2) := by
    simpa [Real.sq_sqrt hepsilon] using
      Real.cosh_le_exp_half_sq (Real.sqrt epsilon)
  have hexpRational :
      Real.exp (epsilon / 2) ≤ 1 / (1 - epsilon / 2) :=
    Real.exp_bound_div_one_sub_of_interval hhalfNonnegative hhalfLtOne
  have hden : 0 < 1 - epsilon / 2 := by linarith
  have hrational : 1 / (1 - epsilon / 2) ≤ 1 + epsilon := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hcosh : Real.cosh (Real.sqrt epsilon) ≤ 1 + epsilon :=
    hcoshExp.trans (hexpRational.trans hrational)
  have harcosh :=
    (Real.arcosh_le_arcosh (Real.cosh_pos _) (by linarith)).2 hcosh
  simpa [Real.arcosh_cosh (Real.sqrt_nonneg epsilon)] using harcosh

theorem half_exp_le_abs_eval_chebyshev_one_add
    (degree : Nat) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1) :
    Real.exp ((degree : ℝ) * Real.sqrt epsilon) / 2 ≤
      |(Polynomial.Chebyshev.T ℝ degree).eval (1 + epsilon)| := by
  have harcosh := sqrt_le_arcosh_one_add hepsilon hepsilonOne
  have hscaled :
      (degree : ℝ) * Real.sqrt epsilon ≤
        (degree : ℝ) * Real.arcosh (1 + epsilon) :=
    mul_le_mul_of_nonneg_left harcosh (Nat.cast_nonneg degree)
  have heval :
      (Polynomial.Chebyshev.T ℝ degree).eval (1 + epsilon) =
        Real.cosh ((degree : ℝ) * Real.arcosh (1 + epsilon)) := by
    calc
      (Polynomial.Chebyshev.T ℝ degree).eval (1 + epsilon) =
          (Polynomial.Chebyshev.T ℝ degree).eval
            (Real.cosh (Real.arcosh (1 + epsilon))) := by
        rw [Real.cosh_arcosh (by linarith)]
      _ = Real.cosh ((degree : ℝ) * Real.arcosh (1 + epsilon)) := by
        simp
  rw [heval, abs_of_pos (Real.cosh_pos _)]
  calc
    Real.exp ((degree : ℝ) * Real.sqrt epsilon) / 2 ≤
        Real.exp ((degree : ℝ) * Real.arcosh (1 + epsilon)) / 2 := by
      gcongr
    _ ≤ Real.cosh ((degree : ℝ) * Real.arcosh (1 + epsilon)) := by
      rw [Real.cosh_eq]
      have hpositive :
          0 < Real.exp (-((degree : ℝ) * Real.arcosh (1 + epsilon))) :=
        Real.exp_pos _
      linarith

theorem six_le_exp_two : (6 : ℝ) ≤ Real.exp 2 := by
  have hseries :=
    Real.sum_le_exp_of_nonneg (x := (2 : ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hseries ⊢
  linarith

theorem negOnePow_mul_eval_chebyshev_neg_one_sub
    (degree : Nat) (epsilon : ℝ) :
    (-1 : ℝ) ^ degree *
        (Polynomial.Chebyshev.T ℝ degree).eval (-1 - epsilon) =
      (Polynomial.Chebyshev.T ℝ degree).eval (1 + epsilon) := by
  have h :=
    (Polynomial.Chebyshev.T_eval_neg (R := ℝ) (degree : ℤ)
      (-(1 + epsilon))).symm
  rw [Int.cast_negOnePow, zpow_natCast] at h
  convert h using 1 <;> ring_nf

theorem three_le_signed_eval_chebyshev_neg_one_sub
    (degree : Nat) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hexponent : 2 ≤ (degree : ℝ) * Real.sqrt epsilon) :
    3 ≤ (-1 : ℝ) ^ degree *
      (Polynomial.Chebyshev.T ℝ degree).eval (-1 - epsilon) := by
  rw [negOnePow_mul_eval_chebyshev_neg_one_sub]
  have hhalf :=
    half_exp_le_abs_eval_chebyshev_one_add degree hepsilon hepsilonOne
  have hevalNonnegative :
      0 ≤ (Polynomial.Chebyshev.T ℝ degree).eval (1 + epsilon) :=
    (Polynomial.Chebyshev.one_le_eval_T_real (degree : ℤ) (by linarith)).trans'
      zero_le_one
  rw [abs_of_nonneg hevalNonnegative] at hhalf
  calc
    (3 : ℝ) ≤ Real.exp 2 / 2 := by linarith [six_le_exp_two]
    _ ≤ Real.exp ((degree : ℝ) * Real.sqrt epsilon) / 2 := by
      gcongr
    _ ≤ (Polynomial.Chebyshev.T ℝ degree).eval (1 + epsilon) := hhalf

theorem le_abs_eval_chebyshev_neg_one_sub
    (degree : Nat) {epsilon M : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hM : 0 < M)
    (hexponent :
      Real.log (2 * M) ≤ (degree : ℝ) * Real.sqrt epsilon) :
    M ≤ |(Polynomial.Chebyshev.T ℝ degree).eval (-1 - epsilon)| := by
  have hhalf :=
    half_exp_le_abs_eval_chebyshev_one_add degree hepsilon hepsilonOne
  have habs :
      |(Polynomial.Chebyshev.T ℝ degree).eval (-1 - epsilon)| =
        |(Polynomial.Chebyshev.T ℝ degree).eval (1 + epsilon)| := by
    rw [show -1 - epsilon = -(1 + epsilon) by ring,
      Polynomial.Chebyshev.T_eval_neg, abs_mul, abs_unit_intCast, one_mul]
  rw [habs]
  calc
    M = Real.exp (Real.log (2 * M)) / 2 := by
      rw [Real.exp_log (by positivity)]
      ring
    _ ≤ Real.exp ((degree : ℝ) * Real.sqrt epsilon) / 2 := by
      gcongr
    _ ≤ |(Polynomial.Chebyshev.T ℝ degree).eval (1 + epsilon)| := hhalf

theorem one_le_abs_sub_negOnePow_div_two
    (degree : Nat) (value : ℝ)
    (hgrowth : 3 ≤ (-1 : ℝ) ^ degree * value) :
    1 ≤ |(value - (-1 : ℝ) ^ degree) / 2| := by
  rcases neg_one_pow_eq_or ℝ degree with hsign | hsign
  · rw [hsign] at hgrowth ⊢
    rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [hsign] at hgrowth ⊢
    rw [abs_of_nonpos (by linarith)]
    linarith

theorem one_le_abs_eval_correctionFactor_zero_of_signed_growth
    {k i degree : Nat}
    (hgrowth :
      3 ≤ (-1 : ℝ) ^ degree *
        (Polynomial.Chebyshev.T ℝ degree).eval
          (affineArgument k i 0)) :
    1 ≤ |(correctionFactor k i degree).eval 0| := by
  rw [eval_correctionFactor]
  simpa using one_le_abs_sub_negOnePow_div_two degree
    ((Polynomial.Chebyshev.T ℝ degree).eval (affineArgument k i 0)) hgrowth

def appendixMainDegree (k t : Nat) (M : ℝ) : Nat :=
  ⌈Real.sqrt ((k : ℝ) / (t : ℝ) - 1) * Real.log (2 * M)⌉₊

def appendixCorrectionDegree (k i : Nat) : Nat :=
  ⌈2 * Real.sqrt ((k : ℝ) / (i : ℝ) - 1)⌉₊


theorem one_div_sqrt_nat_succ_le_two_mul_sqrt_sub (index : Nat) :
    1 / Real.sqrt ((index + 1 : Nat) : ℝ) ≤
      2 * (Real.sqrt ((index + 1 : Nat) : ℝ) -
        Real.sqrt (index : ℝ)) := by
  let upper := Real.sqrt ((index + 1 : Nat) : ℝ)
  let lower := Real.sqrt (index : ℝ)
  have hupperPositive : 0 < upper := by
    dsimp [upper]
    rw [Real.sqrt_pos]
    positivity
  have hlowerUpper : lower ≤ upper := by
    dsimp [lower, upper]
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.le_succ index
  have hupperSquare : upper * upper = (index + 1 : Nat) := by
    dsimp [upper]
    rw [Real.mul_self_sqrt]
    positivity
  have hlowerSquare : lower * lower = index := by
    dsimp [lower]
    rw [Real.mul_self_sqrt]
    positivity
  have hfactorization :
      (upper - lower) * (upper + lower) = 1 := by
    push_cast at hupperSquare hlowerSquare
    nlinarith
  have hone : 1 ≤ 2 * upper * (upper - lower) := by
    calc
      (1 : ℝ) = (upper - lower) * (upper + lower) := hfactorization.symm
      _ ≤ (upper - lower) * (2 * upper) := by
        apply mul_le_mul_of_nonneg_left
        · linarith
        · exact sub_nonneg.mpr hlowerUpper
      _ = 2 * upper * (upper - lower) := by ring
  have hdiv : 1 / upper ≤ 2 * (upper - lower) := by
    rw [div_le_iff₀ hupperPositive]
    nlinarith
  simpa [upper, lower] using hdiv

theorem sum_one_div_sqrt_le_two_mul_sqrt (t : Nat) :
    (∑ i ∈ Finset.Ico 1 t, 1 / Real.sqrt (i : ℝ)) ≤
      2 * Real.sqrt (t : ℝ) := by
  have htelescoping (length : Nat) :
      (∑ index ∈ Finset.range length,
          (Real.sqrt ((index + 1 : Nat) : ℝ) -
            Real.sqrt (index : ℝ))) = Real.sqrt (length : ℝ) := by
    induction length with
    | zero => simp
    | succ length ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  calc
    (∑ i ∈ Finset.Ico 1 t, 1 / Real.sqrt (i : ℝ)) =
        ∑ index ∈ Finset.range (t - 1),
          1 / Real.sqrt ((1 + index : Nat) : ℝ) := by
      rw [Finset.sum_Ico_eq_sum_range]
    _ ≤ ∑ index ∈ Finset.range (t - 1),
        2 * (Real.sqrt ((index + 1 : Nat) : ℝ) -
          Real.sqrt (index : ℝ)) := by
      apply Finset.sum_le_sum
      intro index hindex
      simpa [add_comm] using
        one_div_sqrt_nat_succ_le_two_mul_sqrt_sub index
    _ = 2 * Real.sqrt ((t - 1 : Nat) : ℝ) := by
      rw [← Finset.mul_sum, htelescoping]
    _ ≤ 2 * Real.sqrt (t : ℝ) := by
      gcongr
      exact_mod_cast Nat.sub_le t 1

theorem sum_sqrt_ratio_sub_one_le_two_mul_sqrt_mul (k t : Nat) :
    (∑ i ∈ Finset.Ico 1 t,
        Real.sqrt ((k : ℝ) / (i : ℝ) - 1)) ≤
      2 * Real.sqrt ((k : ℝ) * (t : ℝ)) := by
  calc
    (∑ i ∈ Finset.Ico 1 t,
        Real.sqrt ((k : ℝ) / (i : ℝ) - 1)) ≤
        ∑ i ∈ Finset.Ico 1 t,
          Real.sqrt (k : ℝ) * (1 / Real.sqrt (i : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        Real.sqrt ((k : ℝ) / (i : ℝ) - 1) ≤
            Real.sqrt ((k : ℝ) / (i : ℝ)) := by
          apply Real.sqrt_le_sqrt
          linarith
        _ = Real.sqrt (k : ℝ) / Real.sqrt (i : ℝ) := by
          rw [Real.sqrt_div (Nat.cast_nonneg k)]
        _ = Real.sqrt (k : ℝ) * (1 / Real.sqrt (i : ℝ)) := by
          ring
    _ = Real.sqrt (k : ℝ) *
        (∑ i ∈ Finset.Ico 1 t, 1 / Real.sqrt (i : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ Real.sqrt (k : ℝ) * (2 * Real.sqrt (t : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact sum_one_div_sqrt_le_two_mul_sqrt t
      · exact Real.sqrt_nonneg _
    _ = 2 * Real.sqrt ((k : ℝ) * (t : ℝ)) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg k)]
      ring

theorem cast_appendixMainDegree_le
    (k t : Nat) {M : ℝ} (hM : 1 ≤ M) :
    (appendixMainDegree k t M : ℝ) ≤
      Real.sqrt ((k : ℝ) / (t : ℝ)) * Real.log (2 * M) + 1 := by
  have hlog : 0 ≤ Real.log (2 * M) := by
    apply Real.log_nonneg
    nlinarith
  have hrawNonnegative :
      0 ≤ Real.sqrt ((k : ℝ) / (t : ℝ) - 1) * Real.log (2 * M) :=
    mul_nonneg (Real.sqrt_nonneg _) hlog
  calc
    (appendixMainDegree k t M : ℝ) ≤
        Real.sqrt ((k : ℝ) / (t : ℝ) - 1) * Real.log (2 * M) + 1 := by
      exact (Nat.ceil_lt_add_one hrawNonnegative).le
    _ ≤ Real.sqrt ((k : ℝ) / (t : ℝ)) * Real.log (2 * M) + 1 := by
      have hsqrt :
          Real.sqrt ((k : ℝ) / (t : ℝ) - 1) ≤
            Real.sqrt ((k : ℝ) / (t : ℝ)) := by
        apply Real.sqrt_le_sqrt
        linarith
      have hproduct := mul_le_mul_of_nonneg_right hsqrt hlog
      linarith

theorem cast_sum_appendixCorrectionDegree_le (k t : Nat) :
    ((∑ i ∈ Finset.Ico 1 t, appendixCorrectionDegree k i : Nat) : ℝ) ≤
      4 * Real.sqrt ((k : ℝ) * (t : ℝ)) + (t : ℝ) := by
  have hcard : ((Finset.Ico 1 t).card : ℝ) ≤ (t : ℝ) := by
    norm_cast
    exact (Finset.card_le_card (Finset.Ico_subset_Iio_self)).trans (by simp)
  calc
    ((∑ i ∈ Finset.Ico 1 t, appendixCorrectionDegree k i : Nat) : ℝ) =
        ∑ i ∈ Finset.Ico 1 t, (appendixCorrectionDegree k i : ℝ) := by
      push_cast
      rfl
    _ ≤ ∑ i ∈ Finset.Ico 1 t,
        (2 * Real.sqrt ((k : ℝ) / (i : ℝ) - 1) + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Nat.ceil_lt_add_one (by positivity)).le
    _ = 2 * (∑ i ∈ Finset.Ico 1 t,
          Real.sqrt ((k : ℝ) / (i : ℝ) - 1)) +
        ((Finset.Ico 1 t).card : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ 2 * (2 * Real.sqrt ((k : ℝ) * (t : ℝ))) + (t : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (sum_sqrt_ratio_sub_one_le_two_mul_sqrt_mul k t) (by norm_num))
        hcard
    _ = 4 * Real.sqrt ((k : ℝ) * (t : ℝ)) + (t : ℝ) := by ring

theorem cast_appendixDegreeBudget_le
    {k t : Nat} {M : ℝ}
    (_ht : 0 < t) (_htwo : 2 * t ≤ k) (hM : 1 ≤ M) :
    ((appendixMainDegree k t M +
        ∑ i ∈ Finset.Ico 1 t, appendixCorrectionDegree k i : Nat) : ℝ) ≤
      Real.sqrt ((k : ℝ) / (t : ℝ)) * Real.log (2 * M) +
        4 * Real.sqrt ((k : ℝ) * (t : ℝ)) + (t : ℝ) + 1 := by
  calc
    ((appendixMainDegree k t M +
        ∑ i ∈ Finset.Ico 1 t, appendixCorrectionDegree k i : Nat) : ℝ) =
        (appendixMainDegree k t M : ℝ) +
          ((∑ i ∈ Finset.Ico 1 t,
            appendixCorrectionDegree k i : Nat) : ℝ) := by
      push_cast
      rfl
    _ ≤ (Real.sqrt ((k : ℝ) / (t : ℝ)) * Real.log (2 * M) + 1) +
        (4 * Real.sqrt ((k : ℝ) * (t : ℝ)) + (t : ℝ)) :=
      add_le_add (cast_appendixMainDegree_le k t hM)
        (cast_sum_appendixCorrectionDegree_le k t)
    _ = Real.sqrt ((k : ℝ) / (t : ℝ)) * Real.log (2 * M) +
        4 * Real.sqrt ((k : ℝ) * (t : ℝ)) + (t : ℝ) + 1 := by ring

def chosenAppendixPolynomial (k t : Nat) (M : ℝ) : ℝ[X] :=
  appendixPolynomial k t (appendixMainDegree k t M)
    (appendixCorrectionDegree k)

theorem polynomialBounds_chosenAppendixPolynomial_le_nine_pow
    {k t : Nat} (M : ℝ) (ht : 0 < t) (htwo : 2 * t ≤ k) :
    PeakToAveragePolynomialBounds.weightedCoefficientL1
        (chosenAppendixPolynomial k t M) k ≤
      (9 : ℝ) ^
        (appendixMainDegree k t M +
          ∑ i ∈ Finset.Ico 1 t, appendixCorrectionDegree k i) := by
  exact polynomialBounds_appendixPolynomial_le_nine_pow
    (appendixCorrectionDegree k) ht htwo

structure ChosenAppendixGrowth (k t : Nat) (M : ℝ) : Prop where
  cutoff_lt_dimension : t < k
  main :
    M ≤
      |(Polynomial.Chebyshev.T ℝ (appendixMainDegree k t M)).eval
        (affineArgument k t 0)|
  corrections :
    ∀ i ∈ Finset.Ico 1 t,
      3 ≤ (-1 : ℝ) ^ (appendixCorrectionDegree k i) *
        (Polynomial.Chebyshev.T ℝ (appendixCorrectionDegree k i)).eval
          (affineArgument k i 0)

def appendixEpsilon (k i : Nat) : ℝ :=
  (i : ℝ) / ((k : ℝ) - (i : ℝ))

theorem affineArgument_zero_eq_neg_one_sub_appendixEpsilon
    {k i : Nat} (hik : i < k) :
    affineArgument k i 0 = -1 - appendixEpsilon k i := by
  have hden : (k : ℝ) - (i : ℝ) ≠ 0 := by
    have : (i : ℝ) < (k : ℝ) := by exact_mod_cast hik
    linarith
  rw [affineArgument, appendixEpsilon]
  field_simp
  ring

theorem appendixEpsilon_nonnegative
    {k i : Nat} (hik : i < k) :
    0 ≤ appendixEpsilon k i := by
  rw [appendixEpsilon]
  apply div_nonneg
  · exact Nat.cast_nonneg i
  · apply sub_nonneg.mpr
    exact_mod_cast hik.le

theorem appendixEpsilon_le_one
    {k i : Nat} (htwo : 2 * i ≤ k) (hik : i < k) :
    appendixEpsilon k i ≤ 1 := by
  have hden : 0 < (k : ℝ) - (i : ℝ) := by
    apply sub_pos.mpr
    exact_mod_cast hik
  rw [appendixEpsilon, div_le_iff₀ hden]
  have htwoReal : (2 : ℝ) * i ≤ k := by exact_mod_cast htwo
  linarith

theorem sqrt_ratio_sub_one_mul_sqrt_appendixEpsilon
    {k i : Nat} (hi : 0 < i) (hik : i < k) :
    Real.sqrt ((k : ℝ) / (i : ℝ) - 1) *
        Real.sqrt (appendixEpsilon k i) = 1 := by
  have hiReal : 0 < (i : ℝ) := by exact_mod_cast hi
  have hdiffReal : 0 < (k : ℝ) - (i : ℝ) := by
    apply sub_pos.mpr
    exact_mod_cast hik
  have hratio :
      (k : ℝ) / (i : ℝ) - 1 =
        ((k : ℝ) - (i : ℝ)) / (i : ℝ) := by
    field_simp
  have hfirstNonnegative :
      0 ≤ ((k : ℝ) - (i : ℝ)) / (i : ℝ) := by positivity
  rw [hratio, appendixEpsilon, ← Real.sqrt_mul hfirstNonnegative]
  have hproduct :
      (((k : ℝ) - (i : ℝ)) / (i : ℝ)) *
          ((i : ℝ) / ((k : ℝ) - (i : ℝ))) = 1 := by
    field_simp
  rw [hproduct]
  norm_num

theorem log_le_appendixMainDegree_mul_sqrt_appendixEpsilon
    {k t : Nat} (M : ℝ) (ht : 0 < t) (htk : t < k) :
    Real.log (2 * M) ≤
      (appendixMainDegree k t M : ℝ) *
        Real.sqrt (appendixEpsilon k t) := by
  let rawDegree :=
    Real.sqrt ((k : ℝ) / (t : ℝ) - 1) * Real.log (2 * M)
  have hceil : rawDegree ≤ (appendixMainDegree k t M : ℝ) := by
    exact Nat.le_ceil rawDegree
  have hsqrtNonnegative : 0 ≤ Real.sqrt (appendixEpsilon k t) :=
    Real.sqrt_nonneg _
  have hmultiplied :=
    mul_le_mul_of_nonneg_right hceil hsqrtNonnegative
  have hreciprocal :=
    sqrt_ratio_sub_one_mul_sqrt_appendixEpsilon ht htk
  dsimp [rawDegree] at hmultiplied
  calc
    Real.log (2 * M) =
        (Real.sqrt ((k : ℝ) / (t : ℝ) - 1) * Real.log (2 * M)) *
          Real.sqrt (appendixEpsilon k t) := by
      rw [mul_assoc, mul_comm (Real.log (2 * M)), ← mul_assoc, hreciprocal,
        one_mul]
    _ ≤ (appendixMainDegree k t M : ℝ) *
        Real.sqrt (appendixEpsilon k t) := hmultiplied

theorem two_le_appendixCorrectionDegree_mul_sqrt_appendixEpsilon
    {k i : Nat} (hi : 0 < i) (hik : i < k) :
    2 ≤ (appendixCorrectionDegree k i : ℝ) *
      Real.sqrt (appendixEpsilon k i) := by
  let rawDegree := 2 * Real.sqrt ((k : ℝ) / (i : ℝ) - 1)
  have hceil : rawDegree ≤ (appendixCorrectionDegree k i : ℝ) := by
    exact Nat.le_ceil rawDegree
  have hsqrtNonnegative : 0 ≤ Real.sqrt (appendixEpsilon k i) :=
    Real.sqrt_nonneg _
  have hmultiplied :=
    mul_le_mul_of_nonneg_right hceil hsqrtNonnegative
  have hreciprocal :=
    sqrt_ratio_sub_one_mul_sqrt_appendixEpsilon hi hik
  dsimp [rawDegree] at hmultiplied
  calc
    (2 : ℝ) =
        (2 * Real.sqrt ((k : ℝ) / (i : ℝ) - 1)) *
          Real.sqrt (appendixEpsilon k i) := by
      rw [mul_assoc, hreciprocal, mul_one]
    _ ≤ (appendixCorrectionDegree k i : ℝ) *
        Real.sqrt (appendixEpsilon k i) := hmultiplied

theorem chosenAppendixGrowth_of_two_mul_cutoff_le
    {k t : Nat} {M : ℝ}
    (ht : 0 < t) (htwo : 2 * t ≤ k) (hM : 0 < M) :
    ChosenAppendixGrowth k t M := by
  have htk : t < k := by omega
  refine
    { cutoff_lt_dimension := htk
      main := ?_
      corrections := ?_ }
  · rw [affineArgument_zero_eq_neg_one_sub_appendixEpsilon htk]
    apply le_abs_eval_chebyshev_neg_one_sub
    · exact appendixEpsilon_nonnegative htk
    · exact appendixEpsilon_le_one htwo htk
    · exact hM
    · exact log_le_appendixMainDegree_mul_sqrt_appendixEpsilon M ht htk
  · intro i hiRange
    have hiBounds := Finset.mem_Ico.mp hiRange
    have hiPositive : 0 < i := hiBounds.1
    have hik : i < k := hiBounds.2.trans htk
    have htwoI : 2 * i ≤ k := by omega
    rw [affineArgument_zero_eq_neg_one_sub_appendixEpsilon hik]
    apply three_le_signed_eval_chebyshev_neg_one_sub
    · exact appendixEpsilon_nonnegative hik
    · exact appendixEpsilon_le_one htwoI hik
    · exact two_le_appendixCorrectionDegree_mul_sqrt_appendixEpsilon
        hiPositive hik

structure UnivariateCertificateData (k : Nat) (M : ℝ) where
  polynomial : ℝ[X]
  large_at_zero : M ≤ |polynomial.eval 0|
  bounded_on_positive_weights :
    ∀ weight : Nat, 1 ≤ weight → weight ≤ k →
      |polynomial.eval (weight : ℝ)| ≤ 1

structure AppendixGrowthConditions
    (k t mainDegree : Nat) (correctionDegree : Nat → Nat) (M : ℝ) : Prop where
  cutoff_lt_dimension : t < k
  main_at_zero :
    M ≤ |(mainFactor k t mainDegree).eval 0|
  correction_at_zero :
    ∀ i ∈ Finset.Ico 1 t,
      1 ≤ |(correctionFactor k i (correctionDegree i)).eval 0|

def ChosenAppendixGrowth.toAppendixGrowthConditions
    {k t : Nat} {M : ℝ} (growth : ChosenAppendixGrowth k t M) :
    AppendixGrowthConditions k t (appendixMainDegree k t M)
      (appendixCorrectionDegree k) M where
  cutoff_lt_dimension := growth.cutoff_lt_dimension
  main_at_zero := by
    simpa using growth.main
  correction_at_zero := by
    intro i hi
    exact one_le_abs_eval_correctionFactor_zero_of_signed_growth
      (growth.corrections i hi)

def AppendixGrowthConditions.toUnivariateCertificateData
    {k t mainDegree : Nat} {correctionDegree : Nat → Nat} {M : ℝ}
    (growth :
      AppendixGrowthConditions k t mainDegree correctionDegree M) :
    UnivariateCertificateData k M where
  polynomial := appendixPolynomial k t mainDegree correctionDegree
  large_at_zero := by
    rw [eval_appendixPolynomial, abs_mul, abs_prod]
    refine growth.main_at_zero.trans ?_
    exact le_mul_of_one_le_right (abs_nonneg _)
      (Finset.one_le_prod fun i hi => growth.correction_at_zero i hi)
  bounded_on_positive_weights := by
    intro weight hweightPositive hweightLe
    by_cases hweightSmall : weight < t
    · rw [eval_appendixPolynomial]
      have hweightK : weight < k :=
        hweightSmall.trans growth.cutoff_lt_dimension
      have hzero :
          (∏ i ∈ Finset.Ico 1 t,
            (correctionFactor k i (correctionDegree i)).eval (weight : ℝ)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_Ico.mpr ⟨hweightPositive, hweightSmall⟩)
        exact eval_correctionFactor_at_index hweightK
      rw [hzero]
      simp
    · have htWeight : t ≤ weight := Nat.le_of_not_gt hweightSmall
      rw [eval_appendixPolynomial, abs_mul, abs_prod]
      have hmain :
          |(mainFactor k t mainDegree).eval (weight : ℝ)| ≤ 1 := by
        apply abs_eval_mainFactor_le_one mainDegree growth.cutoff_lt_dimension
        · exact_mod_cast htWeight
        · exact_mod_cast hweightLe
      have hcorrection :
          (∏ i ∈ Finset.Ico 1 t,
              |(correctionFactor k i (correctionDegree i)).eval (weight : ℝ)|) ≤ 1 := by
        apply Finset.prod_le_one
        · intro i hi
          exact abs_nonneg _
        · intro i hi
          have hiBounds := Finset.mem_Ico.mp hi
          have hiK : i < k := hiBounds.2.trans growth.cutoff_lt_dimension
          apply abs_eval_correctionFactor_le_one hiK
          · exact_mod_cast (hiBounds.2.le.trans htWeight)
          · exact_mod_cast hweightLe
      exact (mul_le_mul hmain hcorrection
        (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by norm_num)).trans_eq
          (by norm_num)

def UnivariateCertificateData.toAndCertificate {k : Nat} {M : ℝ}
    (data : UnivariateCertificateData k M) :
    AndCertificate k data.polynomial.natDegree M where
  coefficient := newtonCoefficient data.polynomial
  degree_le := by
    intro coordinates hnonzero
    exact Nat.le_of_not_gt fun hdegree =>
      hnonzero (newtonCoefficient_eq_zero_of_natDegree_lt
        data.polynomial coordinates hdegree)
  large_at_zero := by
    simpa [evaluate_newtonCoefficient] using data.large_at_zero
  bounded_off_zero := by
    intro point hpoint
    rw [evaluate_newtonCoefficient]
    apply data.bounded_on_positive_weights
    · rw [Nat.one_le_iff_ne_zero, Finset.card_ne_zero]
      rw [Finset.nonempty_iff_ne_empty]
      exact fun hempty => hpoint ((trueCoordinates_eq_empty_iff point).mp hempty)
    · exact card_trueCoordinates_le point

theorem UnivariateCertificateData.coefficientL1_toAndCertificate_le
    {k : Nat} {M : ℝ} (data : UnivariateCertificateData k M) :
    data.toAndCertificate.coefficientL1 ≤
      weightedCoefficientL1 data.polynomial k := by
  exact sum_abs_newtonCoefficient_le_weightedCoefficientL1 k data.polynomial

def ChosenAppendixGrowth.toAndCertificate
    {k t : Nat} {M : ℝ} (growth : ChosenAppendixGrowth k t M) :
    AndCertificate k (chosenAppendixPolynomial k t M).natDegree M :=
  growth.toAppendixGrowthConditions.toUnivariateCertificateData.toAndCertificate

theorem natDegree_chosenAppendixPolynomial_le
    (k t : Nat) (M : ℝ) :
    (chosenAppendixPolynomial k t M).natDegree ≤
      appendixMainDegree k t M +
        ∑ i ∈ Finset.Ico 1 t, appendixCorrectionDegree k i := by
  exact natDegree_appendixPolynomial_le k t (appendixMainDegree k t M)
    (appendixCorrectionDegree k)

theorem cast_natDegree_chosenAppendixPolynomial_le_explicit
    {k t : Nat} {M : ℝ}
    (ht : 0 < t) (htwo : 2 * t ≤ k) (hM : 1 ≤ M) :
    ((chosenAppendixPolynomial k t M).natDegree : ℝ) ≤
      Real.sqrt ((k : ℝ) / (t : ℝ)) * Real.log (2 * M) +
        4 * Real.sqrt ((k : ℝ) * (t : ℝ)) + (t : ℝ) + 1 := by
  calc
    ((chosenAppendixPolynomial k t M).natDegree : ℝ) ≤
        ((appendixMainDegree k t M +
          ∑ i ∈ Finset.Ico 1 t, appendixCorrectionDegree k i : Nat) : ℝ) := by
      exact_mod_cast natDegree_chosenAppendixPolynomial_le k t M
    _ ≤ Real.sqrt ((k : ℝ) / (t : ℝ)) * Real.log (2 * M) +
        4 * Real.sqrt ((k : ℝ) * (t : ℝ)) + (t : ℝ) + 1 :=
      cast_appendixDegreeBudget_le ht htwo hM

theorem ChosenAppendixGrowth.coefficientL1_toAndCertificate_le
    {k t : Nat} {M : ℝ} (growth : ChosenAppendixGrowth k t M) :
    growth.toAndCertificate.coefficientL1 ≤
      weightedCoefficientL1 (chosenAppendixPolynomial k t M) k := by
  exact
    growth.toAppendixGrowthConditions.toUnivariateCertificateData
      |>.coefficientL1_toAndCertificate_le

def explicitAppendixCertificate
    {k t : Nat} {M : ℝ}
    (ht : 0 < t) (htwo : 2 * t ≤ k) (hM : 0 < M) :
    AndCertificate k (chosenAppendixPolynomial k t M).natDegree M :=
  (chosenAppendixGrowth_of_two_mul_cutoff_le ht htwo hM).toAndCertificate

theorem explicitAppendixCertificate_coefficientL1_le
    {k t : Nat} {M : ℝ}
    (ht : 0 < t) (htwo : 2 * t ≤ k) (hM : 0 < M) :
    (explicitAppendixCertificate ht htwo hM).coefficientL1 ≤
      weightedCoefficientL1 (chosenAppendixPolynomial k t M) k :=
  (chosenAppendixGrowth_of_two_mul_cutoff_le ht htwo hM)
    |>.coefficientL1_toAndCertificate_le

theorem explicitAppendixCertificate_coefficientL1_le_polynomialBounds
    {k t : Nat} {M : ℝ}
    (ht : 0 < t) (htwo : 2 * t ≤ k) (hM : 0 < M) :
    (explicitAppendixCertificate ht htwo hM).coefficientL1 ≤
      PeakToAveragePolynomialBounds.weightedCoefficientL1
        (chosenAppendixPolynomial k t M) k := by
  rw [← weightedCoefficientL1_eq_polynomialBounds]
  exact explicitAppendixCertificate_coefficientL1_le ht htwo hM

theorem explicitAppendixCertificate_coefficientL1_le_nine_pow
    {k t : Nat} {M : ℝ}
    (ht : 0 < t) (htwo : 2 * t ≤ k) (hM : 0 < M) :
    (explicitAppendixCertificate ht htwo hM).coefficientL1 ≤
      (9 : ℝ) ^
        (appendixMainDegree k t M +
          ∑ i ∈ Finset.Ico 1 t, appendixCorrectionDegree k i) := by
  exact
    (explicitAppendixCertificate_coefficientL1_le_polynomialBounds
      ht htwo hM).trans
        (polynomialBounds_chosenAppendixPolynomial_le_nine_pow M ht htwo)

end

end PegSeparation.External.PeakToAverageChebyshev
