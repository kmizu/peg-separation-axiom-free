import Mathlib


namespace PegSeparation.LowerBound.MessageBound

open scoped BigOperators

noncomputable section

variable {Y Q Z : Type*}


def kernel [Fintype Q] (chi : Q → Y → ℝ) (y y' : Y) : ℝ :=
  (∑ q, chi q y * chi q y') / (Fintype.card Q : ℝ)

lemma expand_kernel [Fintype Y] [Fintype Q] [Nonempty Q]
    (chi : Q → Y → ℝ) (r : Y → ℝ) :
    (∑ q, (∑ y, r y * chi q y) ^ 2) / (Fintype.card Q : ℝ) =
      ∑ y, ∑ y', r y * r y' * kernel chi y y' := by
  classical
  have hexpand :
      (∑ q, (∑ y, r y * chi q y) ^ 2) =
        ∑ y, ∑ y', r y * r y' * (∑ q, chi q y * chi q y') := by
    simp_rw [pow_two, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y' _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hexpand]
  unfold kernel
  simp_rw [← mul_div_assoc]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_div]

lemma delta_majorant_sum [Fintype Y] [DecidableEq Y]
    (r : Y → ℝ) (mu : ℝ) :
    (∑ y, ∑ y', r y * r y' * ((if y = y' then 1 else 0) + mu)) =
      (∑ y, (r y) ^ 2) + mu * (∑ y, r y) ^ 2 := by
  classical
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  · simp [pow_two]
  · rw [pow_two, Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y' _
    ring

lemma kernel_le_delta_add [Fintype Q] [Nonempty Q] [DecidableEq Y]
    (chi : Q → Y → ℝ) (mu : ℝ) (hmu : 0 ≤ mu)
    (hdiag : ∀ y, kernel chi y y ≤ 1)
    (hoff : ∀ y y', y ≠ y' → |kernel chi y y'| ≤ mu)
    (y y' : Y) :
    kernel chi y y' ≤ (if y = y' then 1 else 0) + mu := by
  by_cases h : y = y'
  · subst y'
    simp only [if_pos]
    linarith [hdiag y]
  · simp only [h, if_false, zero_add]
    exact (le_abs_self (kernel chi y y')).trans (hoff y y' h)


lemma meanSquare_le [Fintype Y] [Fintype Q] [Nonempty Q]
    (chi : Q → Y → ℝ) (mu : ℝ) (r : Y → ℝ)
    (hmu : 0 ≤ mu)
    (hr0 : ∀ y, 0 ≤ r y) (hr1 : ∀ y, r y ≤ 1)
    (hdiag : ∀ y, kernel chi y y ≤ 1)
    (hoff : ∀ y y', y ≠ y' → |kernel chi y y'| ≤ mu) :
    (∑ q, (∑ y, r y * chi q y) ^ 2) / (Fintype.card Q : ℝ) ≤
      (∑ y, r y) + mu * (∑ y, r y) ^ 2 := by
  classical
  rw [expand_kernel chi r]
  calc
    (∑ y, ∑ y', r y * r y' * kernel chi y y') ≤
        ∑ y, ∑ y',
          r y * r y' * ((if y = y' then 1 else 0) + mu) := by
      apply Finset.sum_le_sum
      intro y _
      apply Finset.sum_le_sum
      intro y' _
      exact mul_le_mul_of_nonneg_left
        (kernel_le_delta_add chi mu hmu hdiag hoff y y')
        (mul_nonneg (hr0 y) (hr0 y'))
    _ = (∑ y, (r y) ^ 2) + mu * (∑ y, r y) ^ 2 :=
      delta_majorant_sum r mu
    _ ≤ (∑ y, r y) + mu * (∑ y, r y) ^ 2 := by
      gcongr with y
      nlinarith [hr0 y, hr1 y]

lemma sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    √(x + y) ≤ √x + √y := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

lemma encoder_le_one [Fintype Z] [Nonempty Z]
    (enc : Y → Z → ℝ)
    (henc0 : ∀ y z, 0 ≤ enc y z)
    (hrow : ∀ y, ∑ z, enc y z = 1)
    (y : Y) (z : Z) : enc y z ≤ 1 := by
  calc
    enc y z ≤ ∑ z', enc y z' :=
      Finset.single_le_sum (fun z' _ ↦ henc0 y z') (Finset.mem_univ z)
    _ = 1 := hrow y

lemma messageColumnBound [Fintype Y] [Fintype Q] [Fintype Z]
    [Nonempty Q] [Nonempty Z]
    (chi : Q → Y → ℝ) (enc : Y → Z → ℝ) (mu : ℝ)
    (hmu : 0 ≤ mu)
    (henc0 : ∀ y z, 0 ≤ enc y z)
    (hrow : ∀ y, ∑ z, enc y z = 1)
    (hdiag : ∀ y, kernel chi y y ≤ 1)
    (hoff : ∀ y y', y ≠ y' → |kernel chi y y'| ≤ mu)
    (z : Z) :
    (∑ q, |∑ y, enc y z * chi q y|) / (Fintype.card Q : ℝ) ≤
      √(∑ y, enc y z) + √mu * (∑ y, enc y z) := by
  classical
  let a : ℝ := ∑ y, enc y z
  let v : Q → ℝ := fun q ↦ ∑ y, enc y z * chi q y
  let s : ℝ := ∑ q, |v q|
  let C : ℝ := Fintype.card Q
  have hC : 0 < C := by simp only [C]; positivity
  have ha : 0 ≤ a := by
    simp only [a]
    exact Finset.sum_nonneg (fun y _ ↦ henc0 y z)
  have hs : 0 ≤ s := by
    simp only [s]
    positivity
  have hmean :
      (∑ q, (v q) ^ 2) / C ≤ a + mu * a ^ 2 := by
    simpa only [v, C, a] using
      meanSquare_le chi mu (fun y ↦ enc y z) hmu
        (fun y ↦ henc0 y z)
        (fun y ↦ encoder_le_one enc henc0 hrow y z) hdiag hoff
  have hsumSq : (∑ q, (v q) ^ 2) ≤ C * (a + mu * a ^ 2) := by
    simpa only [mul_comm] using (div_le_iff₀ hC).mp hmean
  have hcauchy : s ^ 2 ≤ C * (∑ q, (v q) ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Q ↦ (1 : ℝ)) (fun q ↦ |v q|)
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.cast_ofNat, sq_abs, s, C, mul_one] using h
  have hsquare : s ^ 2 ≤ C ^ 2 * (a + mu * a ^ 2) := by
    calc
      s ^ 2 ≤ C * (∑ q, (v q) ^ 2) := hcauchy
      _ ≤ C * (C * (a + mu * a ^ 2)) :=
        mul_le_mul_of_nonneg_left hsumSq hC.le
      _ = C ^ 2 * (a + mu * a ^ 2) := by ring
  have hnormalized : (s / C) ^ 2 ≤ a + mu * a ^ 2 := by
    rw [div_pow]
    apply (div_le_iff₀ (by positivity : 0 < C ^ 2)).2
    nlinarith
  have hmua : 0 ≤ mu * a ^ 2 := mul_nonneg hmu (sq_nonneg a)
  calc
    (∑ q, |∑ y, enc y z * chi q y|) / (Fintype.card Q : ℝ) =
        s / C := rfl
    _ ≤ √(a + mu * a ^ 2) :=
      (Real.le_sqrt (div_nonneg hs hC.le) (add_nonneg ha hmua)).2 hnormalized
    _ ≤ √a + √(mu * a ^ 2) := sqrt_add_le a (mu * a ^ 2) ha hmua
    _ = √a + √mu * a := by rw [Real.sqrt_mul hmu, Real.sqrt_sq ha]
    _ = √(∑ y, enc y z) + √mu * (∑ y, enc y z) := rfl


def advantage [Fintype Y] [Fintype Q] [Fintype Z]
    (enc : Y → Z → ℝ) (chi : Q → Y → ℝ) : ℝ :=
  (∑ z, (∑ q, |∑ y, enc y z * chi q y|) / (Fintype.card Q : ℝ)) /
    (Fintype.card Y : ℝ)

def signedRows (alpha : Q → ℝ) (chi : Q → Y → ℝ) : Q → Y → ℝ :=
  fun q y ↦ alpha q * chi q y

lemma kernel_signedRows [Fintype Q]
    (alpha : Q → ℝ) (chi : Q → Y → ℝ)
    (halpha : ∀ q, alpha q ^ 2 = 1) (y y' : Y) :
    kernel (signedRows alpha chi) y y' = kernel chi y y' := by
  unfold kernel signedRows
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  rw [show alpha q * chi q y * (alpha q * chi q y') =
      alpha q ^ 2 * (chi q y * chi q y') by ring, halpha]
  ring

lemma advantage_signedRows [Fintype Y] [Fintype Q] [Fintype Z]
    (enc : Y → Z → ℝ) (alpha : Q → ℝ) (chi : Q → Y → ℝ)
    (halpha : ∀ q, |alpha q| = 1) :
    advantage enc (signedRows alpha chi) = advantage enc chi := by
  classical
  unfold advantage
  apply congrArg (fun t : ℝ ↦ t / (Fintype.card Y : ℝ))
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg (fun t : ℝ ↦ t / (Fintype.card Q : ℝ))
  apply Finset.sum_congr rfl
  intro q _
  have hfactor :
      (∑ y, enc y z * signedRows alpha chi q y) =
        alpha q * (∑ y, enc y z * chi q y) := by
    unfold signedRows
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hfactor, abs_mul, halpha, one_mul]

theorem advantage_le_cardRatio [Fintype Y] [Fintype Q] [Fintype Z]
    [Nonempty Y] [Nonempty Q] [Nonempty Z]
    (chi : Q → Y → ℝ) (enc : Y → Z → ℝ) (mu : ℝ)
    (hmu : 0 ≤ mu)
    (henc0 : ∀ y z, 0 ≤ enc y z)
    (hrow : ∀ y, ∑ z, enc y z = 1)
    (hdiag : ∀ y, kernel chi y y ≤ 1)
    (hoff : ∀ y y', y ≠ y' → |kernel chi y y'| ≤ mu) :
    advantage enc chi ≤
      √((Fintype.card Z : ℝ) / (Fintype.card Y : ℝ)) + √mu := by
  classical
  let a : Z → ℝ := fun z ↦ ∑ y, enc y z
  let S : ℝ := ∑ z, √(a z)
  let CY : ℝ := Fintype.card Y
  let CZ : ℝ := Fintype.card Z
  have hCY : 0 < CY := by simp only [CY]; positivity
  have hCZ0 : 0 ≤ CZ := by simp only [CZ]; positivity
  have ha (z : Z) : 0 ≤ a z := by
    simp only [a]
    exact Finset.sum_nonneg (fun y _ ↦ henc0 y z)
  have hmass : ∑ z, a z = CY := by
    simp only [a, CY]
    rw [Finset.sum_comm]
    simp_rw [hrow]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hS : 0 ≤ S := by
    simp only [S]
    positivity
  have hCauchy : S ^ 2 ≤ CZ * CY := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Z ↦ (1 : ℝ)) (fun z ↦ √(a z))
    have h' : S ^ 2 ≤ CZ * (∑ z, a z) := by
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.cast_ofNat, mul_one, Real.sq_sqrt (ha _), S, CZ] using h
    simpa only [hmass] using h'
  have hratioSq : (S / CY) ^ 2 ≤ CZ / CY := by
    rw [div_pow]
    apply (div_le_iff₀ (by positivity : 0 < CY ^ 2)).2
    have heq : (CZ / CY) * CY ^ 2 = CZ * CY := by
      field_simp
    rw [heq]
    exact hCauchy
  have hratio : S / CY ≤ √(CZ / CY) :=
    (Real.le_sqrt (div_nonneg hS hCY.le) (div_nonneg hCZ0 hCY.le)).2 hratioSq
  have hcollapse :
      (∑ z, (√(a z) + √mu * a z)) / CY = S / CY + √mu := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hmass]
    simp only [S]
    field_simp
  calc
    advantage enc chi =
        (∑ z, (∑ q, |∑ y, enc y z * chi q y|) /
          (Fintype.card Q : ℝ)) / CY := rfl
    _ ≤ (∑ z, (√(a z) + √mu * a z)) / CY := by
      apply div_le_div_of_nonneg_right _ hCY.le
      apply Finset.sum_le_sum
      intro z _
      simpa only [a] using
        messageColumnBound chi enc mu hmu henc0 hrow hdiag hoff z
    _ = S / CY + √mu := hcollapse
    _ ≤ √(CZ / CY) + √mu := add_le_add hratio (le_refl _)
    _ = √((Fintype.card Z : ℝ) / (Fintype.card Y : ℝ)) + √mu := rfl


lemma sqrt_two_pow_ratio (c d : ℕ) :
    √(((2 : ℝ) ^ c) / ((2 : ℝ) ^ d)) =
      (2 : ℝ) ^ (((c : ℝ) - (d : ℝ)) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast]
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 2
  ring

theorem advantage_le_bits [Fintype Y] [Fintype Q] [Fintype Z]
    [Nonempty Y] [Nonempty Q] [Nonempty Z]
    (chi : Q → Y → ℝ) (enc : Y → Z → ℝ) (mu : ℝ) (c d : ℕ)
    (hmu : 0 ≤ mu)
    (henc0 : ∀ y z, 0 ≤ enc y z)
    (hrow : ∀ y, ∑ z, enc y z = 1)
    (hdiag : ∀ y, kernel chi y y ≤ 1)
    (hoff : ∀ y y', y ≠ y' → |kernel chi y y'| ≤ mu)
    (hYcard : Fintype.card Y = 2 ^ d)
    (hZcard : Fintype.card Z ≤ 2 ^ c) :
    advantage enc chi ≤
      (2 : ℝ) ^ (((c : ℝ) - (d : ℝ)) / 2) + √mu := by
  have hYreal : (Fintype.card Y : ℝ) = (2 : ℝ) ^ d := by
    exact_mod_cast hYcard
  have hZreal : (Fintype.card Z : ℝ) ≤ (2 : ℝ) ^ c := by
    exact_mod_cast hZcard
  calc
    advantage enc chi ≤
        √((Fintype.card Z : ℝ) / (Fintype.card Y : ℝ)) + √mu :=
      advantage_le_cardRatio chi enc mu hmu henc0 hrow hdiag hoff
    _ ≤ √(((2 : ℝ) ^ c) / ((2 : ℝ) ^ d)) + √mu := by
      apply add_le_add
      · apply Real.sqrt_le_sqrt
        rw [hYreal]
        exact div_le_div_of_nonneg_right hZreal (by positivity)
      · exact le_refl _
    _ = (2 : ℝ) ^ (((c : ℝ) - (d : ℝ)) / 2) + √mu := by
      rw [sqrt_two_pow_ratio]

theorem signedAdvantage_le_bits [Fintype Y] [Fintype Q] [Fintype Z]
    [Nonempty Y] [Nonempty Q] [Nonempty Z]
    (alpha : Q → ℝ) (chi : Q → Y → ℝ) (enc : Y → Z → ℝ)
    (mu : ℝ) (c d : ℕ)
    (halpha : ∀ q, |alpha q| = 1)
    (hmu : 0 ≤ mu)
    (henc0 : ∀ y z, 0 ≤ enc y z)
    (hrow : ∀ y, ∑ z, enc y z = 1)
    (hdiag : ∀ y, kernel chi y y ≤ 1)
    (hoff : ∀ y y', y ≠ y' → |kernel chi y y'| ≤ mu)
    (hYcard : Fintype.card Y = 2 ^ d)
    (hZcard : Fintype.card Z ≤ 2 ^ c) :
    advantage enc (signedRows alpha chi) ≤
      (2 : ℝ) ^ (((c : ℝ) - (d : ℝ)) / 2) + √mu := by
  rw [advantage_signedRows enc alpha chi halpha]
  exact advantage_le_bits chi enc mu c d hmu henc0 hrow hdiag hoff hYcard hZcard

theorem advantage_le_bitVectors {d c : ℕ}
    {Q Z : Type*} [Fintype Q] [Fintype Z] [Nonempty Q] [Nonempty Z]
    (chi : Q → (Fin d → Bool) → ℝ)
    (enc : (Fin d → Bool) → Z → ℝ) (mu : ℝ)
    (hmu : 0 ≤ mu)
    (henc0 : ∀ y z, 0 ≤ enc y z)
    (hrow : ∀ y, ∑ z, enc y z = 1)
    (hdiag : ∀ y, kernel chi y y ≤ 1)
    (hoff : ∀ y y', y ≠ y' → |kernel chi y y'| ≤ mu)
    (hZcard : Fintype.card Z ≤ 2 ^ c) :
    advantage enc chi ≤
      (2 : ℝ) ^ (((c : ℝ) - (d : ℝ)) / 2) + √mu := by
  apply advantage_le_bits chi enc mu c d hmu henc0 hrow hdiag hoff
  · simp
  · exact hZcard

end

end PegSeparation.LowerBound.MessageBound
