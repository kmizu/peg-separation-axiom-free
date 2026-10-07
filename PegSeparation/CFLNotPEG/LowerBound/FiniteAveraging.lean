import PegSeparation.CFLNotPEG.LowerBound.ProtocolBridge


open scoped BigOperators

namespace PegSeparation.LowerBound.FiniteAveraging

noncomputable section


theorem exists_context_of_total_mul_le
    {A B Q : Type*} [Fintype A] [Fintype B] [Fintype Q]
    [Nonempty A] [Nonempty B] [Nonempty Q]
    (charge : A → B → Q → ℕ) (E T : ℕ)
    (hglobal :
      (∑ a : A, ∑ b : B, ∑ q : Q, charge a b q) * E ≤
        Fintype.card A * Fintype.card B * Fintype.card Q * T) :
    ∃ b : B,
      (∑ a : A, ∑ q : Q, charge a b q) * E ≤
        Fintype.card A * Fintype.card Q * T := by
  classical
  by_contra hnone
  push Not at hnone
  have hstrict :
      (∑ _b : B, Fintype.card A * Fintype.card Q * T) <
        ∑ b : B, (∑ a : A, ∑ q : Q, charge a b q) * E := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun b _hb ↦ hnone b)
  have hcontradiction :
      Fintype.card A * Fintype.card B * Fintype.card Q * T <
        (∑ a : A, ∑ b : B, ∑ q : Q, charge a b q) * E := by
    calc
      Fintype.card A * Fintype.card B * Fintype.card Q * T =
          ∑ _b : B, Fintype.card A * Fintype.card Q * T := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
      _ < ∑ b : B, (∑ a : A, ∑ q : Q, charge a b q) * E := hstrict
      _ = (∑ b : B, ∑ a : A, ∑ q : Q, charge a b q) * E := by
        rw [← Finset.sum_mul]
      _ = (∑ a : A, ∑ b : B, ∑ q : Q, charge a b q) * E := by
        rw [Finset.sum_comm]
  exact (Nat.not_lt_of_ge hglobal) hcontradiction


theorem sum_reindex_equiv_prod
    {Full A B R : Type*} [Fintype Full] [Fintype A] [Fintype B]
    [AddCommMonoid R]
    (split : Full ≃ A × B) (f : Full → R) :
    (∑ full : Full, f full) =
      ∑ a : A, ∑ b : B, f (split.symm (a, b)) := by
  classical
  calc
    (∑ full : Full, f full) =
        ∑ pair : A × B, f (split.symm pair) :=
      ((split.symm.sum_comp f).symm)
    _ = ∑ a : A, ∑ b : B, f (split.symm (a, b)) :=
      Fintype.sum_prod_type _

theorem sum_reindex_prod_equiv
    {Full A B R : Type*} [Fintype Full] [Fintype A] [Fintype B]
    [AddCommMonoid R]
    (assemble : A × B ≃ Full) (f : Full → R) :
    (∑ full : Full, f full) =
      ∑ a : A, ∑ b : B, f (assemble (a, b)) := by
  simpa using sum_reindex_equiv_prod assemble.symm f


def uniformNatExpectation
    {A Q : Type} [Fintype A] [Fintype Q]
    [Nonempty A] [Nonempty Q]
    (cost : A → Q → ℕ) : ℝ :=
  ∑ a : A, (ProtocolBridge.uniformFiniteDistribution A).mass a *
    ∑ q : Q, (ProtocolBridge.uniformFiniteDistribution Q).mass q *
      (cost a q : ℝ)

theorem uniformNatExpectation_eq_total_div_card
    {A Q : Type} [Fintype A] [Fintype Q]
    [Nonempty A] [Nonempty Q]
    (cost : A → Q → ℕ) :
    uniformNatExpectation cost =
      ((∑ a : A, ∑ q : Q, cost a q : ℕ) : ℝ) /
        ((Fintype.card A : ℝ) * (Fintype.card Q : ℝ)) := by
  classical
  let cardA : ℝ := Fintype.card A
  let cardQ : ℝ := Fintype.card Q
  have hcardA : 0 < cardA := by
    simp only [cardA]
    positivity
  have hcardQ : 0 < cardQ := by
    simp only [cardQ]
    positivity
  have hcast :
      (∑ a : A, ∑ q : Q, (cost a q : ℝ)) =
        ((∑ a : A, ∑ q : Q, cost a q : ℕ) : ℝ) := by
    norm_cast
  unfold uniformNatExpectation
  simp_rw [ProtocolBridge.uniformFiniteDistribution_mass]
  change
    (∑ a : A, (1 / cardA) *
      ∑ q : Q, (1 / cardQ) * (cost a q : ℝ)) = _
  calc
    (∑ a : A, (1 / cardA) *
        ∑ q : Q, (1 / cardQ) * (cost a q : ℝ)) =
        (1 / cardA) *
          ∑ a : A, ∑ q : Q, (1 / cardQ) * (cost a q : ℝ) := by
      rw [Finset.mul_sum]
    _ = (1 / cardA) *
        ∑ a : A, (1 / cardQ) * ∑ q : Q, (cost a q : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
    _ = (1 / cardA) * (1 / cardQ) *
        (∑ a : A, ∑ q : Q, (cost a q : ℝ)) := by
      rw [← Finset.mul_sum]
      ring
    _ = (1 / cardA) * (1 / cardQ) *
        ((∑ a : A, ∑ q : Q, cost a q : ℕ) : ℝ) := by
      rw [hcast]
    _ = ((∑ a : A, ∑ q : Q, cost a q : ℕ) : ℝ) /
        ((Fintype.card A : ℝ) * (Fintype.card Q : ℝ)) := by
      simp only [cardA, cardQ]
      field_simp [hcardA.ne', hcardQ.ne']

theorem uniformNatExpectation_le_div_of_total_mul_le
    {A Q : Type} [Fintype A] [Fintype Q]
    [Nonempty A] [Nonempty Q]
    (cost : A → Q → ℕ) (E T : ℕ)
    (hE : 0 < E)
    (hcleared :
      (∑ a : A, ∑ q : Q, cost a q) * E ≤
        Fintype.card A * Fintype.card Q * T) :
    uniformNatExpectation cost ≤ (T : ℝ) / (E : ℝ) := by
  rw [uniformNatExpectation_eq_total_div_card]
  have hcardA : (0 : ℝ) < Fintype.card A := by positivity
  have hcardQ : (0 : ℝ) < Fintype.card Q := by positivity
  have hEr : (0 : ℝ) < E := by exact_mod_cast hE
  have hreal :
      (((∑ a : A, ∑ q : Q, cost a q) : ℕ) : ℝ) * (E : ℝ) ≤
        (Fintype.card A : ℝ) * (Fintype.card Q : ℝ) * (T : ℝ) := by
    exact_mod_cast hcleared
  apply (div_le_div_iff₀ (mul_pos hcardA hcardQ) hEr).2
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hreal

theorem exists_context_uniformNatExpectation_le_div
    {A B Q : Type} [Fintype A] [Fintype B] [Fintype Q]
    [Nonempty A] [Nonempty B] [Nonempty Q]
    (charge : A → B → Q → ℕ) (E T : ℕ)
    (hE : 0 < E)
    (hglobal :
      (∑ a : A, ∑ b : B, ∑ q : Q, charge a b q) * E ≤
        Fintype.card A * Fintype.card B * Fintype.card Q * T) :
    ∃ b : B,
      uniformNatExpectation (fun a q ↦ charge a b q) ≤
        (T : ℝ) / (E : ℝ) := by
  obtain ⟨b, hb⟩ := exists_context_of_total_mul_le charge E T hglobal
  exact ⟨b, uniformNatExpectation_le_div_of_total_mul_le
    (fun a q ↦ charge a b q) E T hE hb⟩

end

end PegSeparation.LowerBound.FiniteAveraging
