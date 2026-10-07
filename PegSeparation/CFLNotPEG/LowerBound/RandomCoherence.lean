import Mathlib


open scoped BigOperators ENNReal NNReal
open Finset MeasureTheory ProbabilityTheory

namespace PegSeparation.LowerBound.RandomCoherence

noncomputable section

abbrev F2 := ZMod 2

abbrev F2Vec (d : ℕ) := Fin d → F2

abbrev RowMatrix (d M : ℕ) := Fin M → F2Vec d

def parityCharacter : AddChar F2 ℝ :=
  AddChar.zmodChar 2 (by norm_num : (-1 : ℝ) ^ 2 = 1)

@[simp]
theorem parityCharacter_apply (x : F2) :
    parityCharacter x = (-1 : ℝ) ^ x.val :=
  rfl

@[simp]
theorem parityCharacter_zero : parityCharacter 0 = 1 := by
  simp [parityCharacter]

@[simp]
theorem parityCharacter_one : parityCharacter 1 = -1 := by
  rw [parityCharacter_apply]
  norm_num [ZMod.val_one]

def dotHom {d : ℕ} (u : F2Vec d) : F2Vec d →+ F2 where
  toFun x := ∑ i, x i * u i
  map_zero' := by simp
  map_add' x y := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dotHom_comm {d : ℕ} (u x : F2Vec d) : dotHom u x = dotHom x u := by
  simp [dotHom, mul_comm]

def rowCharacter {d : ℕ} (u : F2Vec d) : AddChar (F2Vec d) ℝ :=
  parityCharacter.compAddMonoidHom (dotHom u)

@[simp]
theorem rowCharacter_apply {d : ℕ} (u x : F2Vec d) :
    rowCharacter u x = (-1 : ℝ) ^ (dotHom u x).val :=
  rfl

@[simp]
theorem rowCharacter_zero {d : ℕ} : rowCharacter (0 : F2Vec d) = 0 := by
  ext x
  simp [rowCharacter, dotHom]

theorem dotHom_surjective {d : ℕ} {u : F2Vec d} (hu : u ≠ 0) :
    Function.Surjective (dotHom u) := by
  classical
  have hcoord : ∃ i, u i ≠ 0 := by
    apply Classical.not_forall.mp
    intro h
    apply hu
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hcoord
  intro z
  refine ⟨(Pi.single i (z * (u i)⁻¹) : F2Vec d), ?_⟩
  change ∑ j, (Pi.single i (z * (u i)⁻¹) : F2Vec d) j * u j = z
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hji
    simp [hji]
  · simp

theorem rowCharacter_ne_zero {d : ℕ} {u : F2Vec d} (hu : u ≠ 0) :
    rowCharacter u ≠ 0 := by
  have hsurj := dotHom_surjective hu
  have hparity : parityCharacter ≠ 0 := by
    apply (AddChar.zmod_char_ne_one_iff 2 parityCharacter).2
    rw [parityCharacter_one]
    norm_num
  intro hzero
  apply hparity
  apply AddChar.compAddMonoidHom_injective_left (dotHom u) hsurj
  change rowCharacter u = (0 : AddChar F2 ℝ).compAddMonoidHom (dotHom u)
  rw [hzero]
  ext x
  simp

theorem rowCharacter_add {d : ℕ} (u v : F2Vec d) :
    rowCharacter (u + v) = rowCharacter u * rowCharacter v := by
  ext x
  simp only [rowCharacter, AddChar.compAddMonoidHom_apply, AddChar.mul_apply]
  rw [show dotHom (u + v) x = dotHom u x + dotHom v x by
    simp [dotHom, Finset.sum_add_distrib, mul_add]]
  exact AddChar.map_add_eq_mul parityCharacter _ _

theorem expect_rowCharacter_eq_zero {d : ℕ} {u : F2Vec d} (hu : u ≠ 0) :
    𝔼 x : F2Vec d, rowCharacter u x = 0 := by
  apply AddChar.expect_eq_zero_iff_ne_zero.2
  exact rowCharacter_ne_zero hu

theorem expect_rowCharacter_mul (d : ℕ) (u v : F2Vec d) :
    𝔼 x : F2Vec d, rowCharacter u x * rowCharacter v x = if u = v then 1 else 0 := by
  classical
  rw [show (𝔼 x : F2Vec d, rowCharacter u x * rowCharacter v x) =
      𝔼 x : F2Vec d, rowCharacter (u + v) x by
    apply Finset.expect_congr rfl
    intro x _
    exact DFunLike.congr_fun (rowCharacter_add u v).symm x]
  rw [AddChar.expect_eq_ite]
  have hiff : rowCharacter (u + v) = 0 ↔ u = v := by
    constructor
    · intro hchar
      have hsum : u + v = 0 := by
        by_contra hne
        exact rowCharacter_ne_zero hne hchar
      funext i
      exact CharTwo.add_eq_zero.mp (congrFun hsum i)
    · intro huv
      subst v
      have hsum : u + u = 0 := by
        funext i
        exact CharTwo.add_self_eq_zero (u i)
      rw [hsum]
      exact rowCharacter_zero
  simp only [hiff]


def uniformRow (d : ℕ) : Measure (F2Vec d) :=
  (PMF.uniformOfFintype (F2Vec d)).toMeasure

instance instIsProbabilityMeasureUniformRow (d : ℕ) :
    IsProbabilityMeasure (uniformRow d) :=
  PMF.toMeasure.isProbabilityMeasure _

theorem integral_uniformRow_eq_expect (d : ℕ) (f : F2Vec d → ℝ) :
    ∫ x, f x ∂uniformRow d = 𝔼 x : F2Vec d, f x := by
  rw [uniformRow, PMF.integral_eq_tsum]
  · simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, tsum_fintype]
    rw [Fintype.expect_eq_sum_div_card]
    simp only [smul_eq_mul, div_eq_inv_mul, Finset.mul_sum]
  · exact Integrable.of_finite

theorem rowCharacter_eq_neg_one_or_one {d : ℕ} (u x : F2Vec d) :
    rowCharacter u x = -1 ∨ rowCharacter u x = 1 := by
  rw [rowCharacter_apply]
  have hlt := (dotHom u x).val_lt
  have hval : (dotHom u x).val = 0 ∨ (dotHom u x).val = 1 := by omega
  rcases hval with hval | hval
  · exact Or.inr (by simp [hval])
  · exact Or.inl (by simp [hval])

theorem rowCharacter_mem_Icc {d : ℕ} (u x : F2Vec d) :
    rowCharacter u x ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases rowCharacter_eq_neg_one_or_one u x with h | h <;> rw [h] <;> norm_num

theorem rowCharacter_hasSubgaussianMGF {d : ℕ} {u : F2Vec d} (hu : u ≠ 0) :
    HasSubgaussianMGF (rowCharacter u) 1 (uniformRow d) := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (X := fun x : F2Vec d ↦ rowCharacter u x) (a := (-1 : ℝ)) (b := (1 : ℝ))
    (measurable_of_finite _).aemeasurable
    (ae_of_all _ fun x ↦ rowCharacter_mem_Icc u x)
    (by rw [integral_uniformRow_eq_expect, expect_rowCharacter_eq_zero hu])
  norm_num at h ⊢
  exact h

def uniformMatrix (d M : ℕ) : Measure (RowMatrix d M) :=
  Measure.pi fun _ : Fin M ↦ uniformRow d

instance instIsProbabilityMeasureUniformMatrix (d M : ℕ) :
    IsProbabilityMeasure (uniformMatrix d M) := by
  rw [uniformMatrix]
  infer_instance

def characterSum {d M : ℕ} (S : RowMatrix d M) (u : F2Vec d) : ℝ :=
  ∑ q, rowCharacter u (S q)

def kernel {d M : ℕ} (S : RowMatrix d M) (u : F2Vec d) : ℝ :=
  characterSum S u / M

def coherence {d M : ℕ} (S : RowMatrix d M) : ℝ :=
  ↑((Finset.univ : Finset (F2Vec d)).sup fun u ↦
    if u = 0 then 0 else Real.toNNReal |kernel S u|)

theorem coherence_le_of_pointwise {d M : ℕ} {S : RowMatrix d M} {eps : ℝ}
    (heps : 0 ≤ eps) (h : ∀ u : F2Vec d, u ≠ 0 → |kernel S u| ≤ eps) :
    coherence S ≤ eps := by
  have hsup :
      ((Finset.univ : Finset (F2Vec d)).sup fun u ↦
        if u = 0 then 0 else Real.toNNReal |kernel S u|) ≤ Real.toNNReal eps := by
    apply Finset.sup_le
    intro u _
    by_cases hu : u = 0
    · simp [hu]
    · simp only [hu, ↓reduceIte]
      exact Real.toNNReal_mono (h u hu)
  calc
    coherence S ≤ ↑(Real.toNNReal eps) := NNReal.coe_le_coe.2 hsup
    _ = eps := Real.coe_toNNReal eps heps

theorem iIndepFun_rowCharacter (d M : ℕ) (u : F2Vec d) :
    iIndepFun (fun q : Fin M ↦ fun S : RowMatrix d M ↦ rowCharacter u (S q))
      (uniformMatrix d M) := by
  rw [uniformMatrix]
  exact iIndepFun_pi fun _ ↦ (measurable_of_finite (rowCharacter u)).aemeasurable

theorem rowCharacter_eval_hasSubgaussianMGF {d M : ℕ} {u : F2Vec d}
    (hu : u ≠ 0) (q : Fin M) :
    HasSubgaussianMGF (fun S : RowMatrix d M ↦ rowCharacter u (S q)) 1
      (uniformMatrix d M) := by
  let μ : Fin M → Measure (F2Vec d) := fun _ ↦ uniformRow d
  have hp := measurePreserving_eval μ q
  have hmap : (uniformMatrix d M).map (fun S : RowMatrix d M ↦ S q) = uniformRow d := by
    simpa [uniformMatrix, μ] using hp.map_eq
  have hbase := rowCharacter_hasSubgaussianMGF hu
  refine (HasSubgaussianMGF.of_map hp.measurable.aemeasurable ?_).congr
    (ae_of_all _ fun _ ↦ rfl)
  rw [hmap]
  exact hbase

theorem characterSum_hasSubgaussianMGF {d M : ℕ} {u : F2Vec d} (hu : u ≠ 0) :
    HasSubgaussianMGF (fun S : RowMatrix d M ↦ characterSum S u) M
      (uniformMatrix d M) := by
  have hindep := iIndepFun_rowCharacter d M u
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun
    (s := (Finset.univ : Finset (Fin M))) (c := fun _ ↦ (1 : ℝ≥0)) hindep
    (fun q _ ↦ rowCharacter_eval_hasSubgaussianMGF hu q)
  simpa [characterSum] using hsum

theorem measureReal_abs_characterSum_ge_le {d M : ℕ} {u : F2Vec d} (hu : u ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    (uniformMatrix d M).real {S | t ≤ |characterSum S u|} ≤
      2 * Real.exp (-t ^ 2 / (2 * M)) := by
  let X : RowMatrix d M → ℝ := fun S ↦ characterSum S u
  have hX : HasSubgaussianMGF X M (uniformMatrix d M) :=
    characterSum_hasSubgaussianMGF hu
  have hpos : (uniformMatrix d M).real {S | t ≤ X S} ≤
      Real.exp (-t ^ 2 / (2 * M)) := hX.measure_ge_le ht
  have hneg : (uniformMatrix d M).real {S | t ≤ (-X) S} ≤
      Real.exp (-t ^ 2 / (2 * M)) := by
    simpa only [NNReal.coe_natCast] using hX.neg.measure_ge_le ht
  calc
    (uniformMatrix d M).real {S | t ≤ |characterSum S u|}
        ≤ (uniformMatrix d M).real ({S | t ≤ X S} ∪ {S | t ≤ (-X) S}) := by
          apply measureReal_mono (h₂ := by finiteness)
          intro S hS
          simp only [Set.mem_setOf_eq, Set.mem_union]
          exact le_abs.mp hS
    _ ≤ (uniformMatrix d M).real {S | t ≤ X S} +
        (uniformMatrix d M).real {S | t ≤ (-X) S} := measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * M)) + Real.exp (-t ^ 2 / (2 * M)) :=
      add_le_add hpos hneg
    _ = 2 * Real.exp (-t ^ 2 / (2 * M)) := by ring


def badAt {d M : ℕ} (t : ℝ) (u : F2Vec d) : Set (RowMatrix d M) :=
  if u = 0 then ∅ else {S | t < |characterSum S u|}

def badMatrices (d M : ℕ) (t : ℝ) : Set (RowMatrix d M) :=
  ⋃ u : F2Vec d, badAt (M := M) t u

theorem measureReal_badMatrices_le (d M : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (uniformMatrix d M).real (badMatrices d M t) ≤
      Fintype.card (F2Vec d) * (2 * Real.exp (-t ^ 2 / (2 * M))) := by
  calc
    (uniformMatrix d M).real (badMatrices d M t)
        ≤ ∑ u : F2Vec d, (uniformMatrix d M).real (badAt (M := M) t u) := by
          exact measureReal_iUnion_fintype_le _
    _ ≤ ∑ _u : F2Vec d, 2 * Real.exp (-t ^ 2 / (2 * M)) := by
      apply Finset.sum_le_sum
      intro u _
      by_cases hu : u = 0
      · simp [badAt, hu, Real.exp_nonneg]
      · calc
          (uniformMatrix d M).real (badAt (M := M) t u)
              ≤ (uniformMatrix d M).real {S | t ≤ |characterSum S u|} := by
                apply measureReal_mono (h₂ := by finiteness)
                intro S hS
                have hlt : t < |characterSum S u| := by
                  simpa [badAt, hu] using hS
                exact hlt.le
          _ ≤ 2 * Real.exp (-t ^ 2 / (2 * M)) :=
            measureReal_abs_characterSum_ge_le hu ht
    _ = Fintype.card (F2Vec d) * (2 * Real.exp (-t ^ 2 / (2 * M))) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem exists_matrix_of_tail_budget (d M : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hbudget :
      Fintype.card (F2Vec d) * (2 * Real.exp (-t ^ 2 / (2 * M))) < 1) :
    ∃ S : RowMatrix d M, ∀ u : F2Vec d, u ≠ 0 → |characterSum S u| ≤ t := by
  have hbad : (uniformMatrix d M).real (badMatrices d M t) < 1 :=
    (measureReal_badMatrices_le d M ht).trans_lt hbudget
  have hne : badMatrices d M t ≠ Set.univ := by
    intro hall
    rw [hall] at hbad
    simp at hbad
  obtain ⟨S, hS⟩ := Set.nonempty_compl.2 hne
  refine ⟨S, fun u hu ↦ ?_⟩
  by_contra hle
  have hlt : t < |characterSum S u| := lt_of_not_ge hle
  apply hS
  rw [badMatrices, Set.mem_iUnion]
  exact ⟨u, by simp [badAt, hu, hlt]⟩

@[simp]
theorem card_f2Vec (d : ℕ) : Fintype.card (F2Vec d) = 2 ^ d := by
  simp [F2Vec, F2]


def zeroRowAt {d M : ℕ} (q : Fin M) : Set (RowMatrix d M) :=
  {S | S q = 0}

def hasZeroRow (d M : ℕ) : Set (RowMatrix d M) :=
  ⋃ q : Fin M, zeroRowAt (d := d) q

theorem measureReal_uniformRow_singleton_zero (d : ℕ) :
    (uniformRow d).real ({0} : Set (F2Vec d)) = 1 / (2 : ℝ) ^ d := by
  rw [measureReal_def, uniformRow,
    PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton 0)]
  simp [div_eq_mul_inv]

theorem measureReal_zeroRowAt (d M : ℕ) (q : Fin M) :
    (uniformMatrix d M).real (zeroRowAt (d := d) q) = 1 / (2 : ℝ) ^ d := by
  let μ : Fin M → Measure (F2Vec d) := fun _ ↦ uniformRow d
  have hp := measurePreserving_eval μ q
  have hpre : zeroRowAt (d := d) q =
      (fun S : RowMatrix d M ↦ S q) ⁻¹' ({0} : Set (F2Vec d)) := by
    ext S
    simp [zeroRowAt]
  rw [hpre, uniformMatrix]
  rw [hp.measureReal_preimage (measurableSet_singleton 0).nullMeasurableSet]
  exact measureReal_uniformRow_singleton_zero d

theorem measureReal_hasZeroRow_le (d M : ℕ) :
    (uniformMatrix d M).real (hasZeroRow d M) ≤ M / (2 : ℝ) ^ d := by
  calc
    (uniformMatrix d M).real (hasZeroRow d M)
        ≤ ∑ q : Fin M, (uniformMatrix d M).real (zeroRowAt (d := d) q) := by
          exact measureReal_iUnion_fintype_le _
    _ = ∑ _q : Fin M, 1 / (2 : ℝ) ^ d := by
      apply Finset.sum_congr rfl
      intro q _
      exact measureReal_zeroRowAt d M q
    _ = M / (2 : ℝ) ^ d := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem measureReal_bad_or_zero_le (d M : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (uniformMatrix d M).real (badMatrices d M t ∪ hasZeroRow d M) ≤
      Fintype.card (F2Vec d) * (2 * Real.exp (-t ^ 2 / (2 * M))) +
        M / (2 : ℝ) ^ d := by
  calc
    (uniformMatrix d M).real (badMatrices d M t ∪ hasZeroRow d M)
        ≤ (uniformMatrix d M).real (badMatrices d M t) +
          (uniformMatrix d M).real (hasZeroRow d M) := measureReal_union_le _ _
    _ ≤ Fintype.card (F2Vec d) * (2 * Real.exp (-t ^ 2 / (2 * M))) +
        M / (2 : ℝ) ^ d :=
      add_le_add (measureReal_badMatrices_le d M ht) (measureReal_hasZeroRow_le d M)

theorem measureReal_bad_or_zero_lt_quarter (d M : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hcoherence :
      Fintype.card (F2Vec d) * (2 * Real.exp (-t ^ 2 / (2 * M))) < 1 / 8)
    (hzero : (M : ℝ) / (2 : ℝ) ^ d < 1 / 8) :
    (uniformMatrix d M).real (badMatrices d M t ∪ hasZeroRow d M) < 1 / 4 := by
  calc
    (uniformMatrix d M).real (badMatrices d M t ∪ hasZeroRow d M)
        ≤ Fintype.card (F2Vec d) * (2 * Real.exp (-t ^ 2 / (2 * M))) +
          M / (2 : ℝ) ^ d := measureReal_bad_or_zero_le d M ht
    _ < 1 / 8 + 1 / 8 := add_lt_add hcoherence hzero
    _ = 1 / 4 := by norm_num

theorem exists_matrix_no_zero_row_of_eighth_budgets (d M : ℕ) {t : ℝ}
    (ht : 0 ≤ t)
    (hcoherence :
      Fintype.card (F2Vec d) * (2 * Real.exp (-t ^ 2 / (2 * M))) < 1 / 8)
    (hzero : (M : ℝ) / (2 : ℝ) ^ d < 1 / 8) :
    ∃ S : RowMatrix d M,
      (∀ q, S q ≠ 0) ∧ (∀ u : F2Vec d, u ≠ 0 → |characterSum S u| ≤ t) := by
  have hbad :
      (uniformMatrix d M).real (badMatrices d M t ∪ hasZeroRow d M) < 1 :=
    (measureReal_bad_or_zero_lt_quarter d M ht hcoherence hzero).trans (by norm_num)
  have hne : badMatrices d M t ∪ hasZeroRow d M ≠ Set.univ := by
    intro hall
    rw [hall] at hbad
    simp at hbad
  obtain ⟨S, hS⟩ := Set.nonempty_compl.2 hne
  refine ⟨S, ?_, ?_⟩
  · intro q hq
    apply hS
    exact Or.inr (by
      rw [hasZeroRow, Set.mem_iUnion]
      exact ⟨q, hq⟩)
  · intro u hu
    by_contra hle
    apply hS
    apply Or.inl
    rw [badMatrices, Set.mem_iUnion]
    exact ⟨u, by simp [badAt, hu, lt_of_not_ge hle]⟩


def chi {d M : ℕ} (S : RowMatrix d M) (q : Fin M) (y : F2Vec d) : ℝ :=
  rowCharacter (S q) y

@[simp]
theorem chi_eq_rowCharacter {d M : ℕ} (S : RowMatrix d M) (q : Fin M)
    (y : F2Vec d) : chi S q y = rowCharacter (S q) y := rfl

theorem expect_chi_mul (d M : ℕ) (S : RowMatrix d M) (q r : Fin M) :
    𝔼 y : F2Vec d, chi S q y * chi S r y = if S q = S r then 1 else 0 :=
  expect_rowCharacter_mul d (S q) (S r)

theorem expect_chi_mul_diag (d M : ℕ) (S : RowMatrix d M) (q : Fin M) :
    𝔼 y : F2Vec d, chi S q y * chi S q y = 1 := by
  rw [expect_chi_mul]
  simp

theorem expect_chi_mul_offdiag (d M : ℕ) (S : RowMatrix d M) {q r : Fin M}
    (hqr : S q ≠ S r) :
    𝔼 y : F2Vec d, chi S q y * chi S r y = 0 := by
  rw [expect_chi_mul, if_neg hqr]

theorem expect_chi_eq_zero (d M : ℕ) (S : RowMatrix d M) (q : Fin M)
    (hq : S q ≠ 0) :
    𝔼 y : F2Vec d, chi S q y = 0 :=
  expect_rowCharacter_eq_zero hq

theorem kernel_eq_average_chi {d M : ℕ} (S : RowMatrix d M) (u : F2Vec d) :
    kernel S u = (∑ q, chi S q u) / M :=
  by
    simp only [kernel, characterSum, chi]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    rw [rowCharacter_apply, rowCharacter_apply, dotHom_comm]

theorem sqrt_threshold_tail_budget (d M : ℕ) (hd : 2 ≤ d) (hM : 0 < M) :
    Fintype.card (F2Vec d) *
        (2 * Real.exp (-(2 * Real.sqrt ((d : ℝ) * M)) ^ 2 / (2 * M))) < 1 := by
  rw [card_f2Vec]
  push_cast
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdm : 0 ≤ (d : ℝ) * M := by positivity
  have hsquare : (2 * Real.sqrt ((d : ℝ) * M)) ^ 2 = 4 * d * M := by
    rw [mul_pow, Real.sq_sqrt hdm]
    ring
  have hexponent : -(4 * (d : ℝ) * M) / (2 * M) = -(2 * d) := by
    field_simp
    ring
  rw [hsquare, hexponent]
  have hrearrange : (2 : ℝ) ^ d * (2 * Real.exp (-(2 * (d : ℝ)))) =
      (2 : ℝ) ^ (d + 1) * Real.exp (-(2 * (d : ℝ))) := by
    rw [pow_succ]
    ring
  rw [hrearrange]
  calc
    (2 : ℝ) ^ (d + 1) * Real.exp (-(2 * (d : ℝ))) =
        Real.exp (((d + 1 : ℕ) : ℝ) * Real.log 2) *
          Real.exp (-(2 * (d : ℝ))) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = Real.exp ((((d + 1 : ℕ) : ℝ) * Real.log 2) - 2 * (d : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
    _ < Real.exp 0 := by
      rw [Real.exp_lt_exp]
      have hlog0 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1)
      have hlog : Real.log (2 : ℝ) < 1 := by
        norm_num at hlog0 ⊢
        exact hlog0
      have hnpos : (0 : ℝ) < d + 1 := by positivity
      have hmul := mul_lt_mul_of_pos_left hlog hnpos
      norm_num [Nat.cast_add, Nat.cast_one] at hmul ⊢
      nlinarith
    _ = 1 := Real.exp_zero

theorem exists_small_kernel (d M : ℕ) (hd : 2 ≤ d) (hM : 0 < M) :
    ∃ S : RowMatrix d M, ∀ u : F2Vec d, u ≠ 0 →
      |kernel S u| ≤ 2 * Real.sqrt ((d : ℝ) / M) := by
  have ht : 0 ≤ 2 * Real.sqrt ((d : ℝ) * M) := by positivity
  obtain ⟨S, hS⟩ := exists_matrix_of_tail_budget d M ht
    (sqrt_threshold_tail_budget d M hd hM)
  refine ⟨S, fun u hu ↦ ?_⟩
  have hsum := hS u hu
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [kernel, abs_div, abs_of_pos hMr]
  calc
    |characterSum S u| / M ≤ (2 * Real.sqrt ((d : ℝ) * M)) / M :=
      div_le_div_of_nonneg_right hsum hMr.le
    _ = 2 * Real.sqrt ((d : ℝ) / M) := by
      have hdr : (0 : ℝ) ≤ d := by positivity
      have hsM : Real.sqrt (M : ℝ) ≠ 0 := (Real.sqrt_pos.2 hMr).ne'
      rw [Real.sqrt_mul hdr, Real.sqrt_div hdr]
      have hsquare : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = M := by
        nlinarith [Real.sq_sqrt hMr.le]
      have hdiv : Real.sqrt (M : ℝ) / M = 1 / Real.sqrt (M : ℝ) := by
        nth_rewrite 2 [← hsquare]
        field_simp
      calc
        2 * (Real.sqrt (d : ℝ) * Real.sqrt (M : ℝ)) / M =
            2 * Real.sqrt (d : ℝ) * (Real.sqrt (M : ℝ) / M) := by ring
        _ = 2 * Real.sqrt (d : ℝ) * (1 / Real.sqrt (M : ℝ)) := by rw [hdiv]
        _ = 2 * (Real.sqrt (d : ℝ) / Real.sqrt (M : ℝ)) := by ring

theorem exists_small_coherence (d M : ℕ) (hd : 2 ≤ d) (hM : 0 < M) :
    ∃ S : RowMatrix d M, coherence S ≤ 2 * Real.sqrt ((d : ℝ) / M) := by
  obtain ⟨S, hS⟩ := exists_small_kernel d M hd hM
  refine ⟨S, coherence_le_of_pointwise (by positivity) hS⟩

end

end PegSeparation.LowerBound.RandomCoherence
