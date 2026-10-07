import PegSeparation.CFLNotPEG.LowerBound.RandomCoherence


open scoped BigOperators ENNReal NNReal
open Finset MeasureTheory ProbabilityTheory

namespace PegSeparation.LowerBound.RandomCoherence

noncomputable section

theorem four_sqrt_threshold_tail_budget_lt_eighth
    (d M : ℕ) (hd : 2 ≤ d) (hM : 0 < M) :
    Fintype.card (F2Vec d) *
        (2 * Real.exp (-(4 * Real.sqrt ((d : ℝ) * M)) ^ 2 / (2 * M))) <
      1 / 8 := by
  rw [card_f2Vec]
  push_cast
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdm : 0 ≤ (d : ℝ) * M := by positivity
  have hsquare : (4 * Real.sqrt ((d : ℝ) * M)) ^ 2 = 16 * d * M := by
    rw [mul_pow, Real.sq_sqrt hdm]
    ring
  have hexponent : -(16 * (d : ℝ) * M) / (2 * M) = -(8 * d) := by
    field_simp
    ring
  rw [hsquare, hexponent]
  have hrearrange :
      (2 : ℝ) ^ d * (2 * Real.exp (-(8 * (d : ℝ)))) =
        (1 / 8 : ℝ) *
          ((2 : ℝ) ^ (d + 4) * Real.exp (-(8 * (d : ℝ)))) := by
    rw [pow_add]
    norm_num
    ring
  rw [hrearrange]
  have hfactor :
      (2 : ℝ) ^ (d + 4) * Real.exp (-(8 * (d : ℝ))) < 1 := by
    calc
      (2 : ℝ) ^ (d + 4) * Real.exp (-(8 * (d : ℝ))) =
          Real.exp (((d + 4 : ℕ) : ℝ) * Real.log 2) *
            Real.exp (-(8 * (d : ℝ))) := by
              rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp ((((d + 4 : ℕ) : ℝ) * Real.log 2) - 8 * (d : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
      _ < Real.exp 0 := by
        rw [Real.exp_lt_exp]
        have hlog0 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          (by norm_num : (2 : ℝ) ≠ 1)
        have hlog : Real.log (2 : ℝ) < 1 := by
          norm_num at hlog0 ⊢
          exact hlog0
        have hnpos : (0 : ℝ) < d + 4 := by positivity
        have hmul := mul_lt_mul_of_pos_left hlog hnpos
        norm_num [Nat.cast_add] at hmul ⊢
        nlinarith
      _ = 1 := Real.exp_zero
  calc
    (1 / 8 : ℝ) *
          ((2 : ℝ) ^ (d + 4) * Real.exp (-(8 * (d : ℝ)))) <
        (1 / 8 : ℝ) * 1 :=
      mul_lt_mul_of_pos_left hfactor (by norm_num)
    _ = 1 / 8 := by ring

theorem exists_matrix_no_zero_row_kernel_le_four_sqrt
    (d M : ℕ) (hd : 2 ≤ d) (hM : 0 < M)
    (hzero : (M : ℝ) / (2 : ℝ) ^ d < 1 / 8) :
    ∃ S : RowMatrix d M,
      (∀ q, S q ≠ 0) ∧
        (∀ u : F2Vec d, u ≠ 0 → |kernel S u| ≤ 4 * Real.sqrt ((d : ℝ) / M)) := by
  have ht : 0 ≤ 4 * Real.sqrt ((d : ℝ) * M) := by positivity
  obtain ⟨S, hrows, hS⟩ :=
    exists_matrix_no_zero_row_of_eighth_budgets d M ht
      (four_sqrt_threshold_tail_budget_lt_eighth d M hd hM) hzero
  refine ⟨S, hrows, fun u hu ↦ ?_⟩
  have hsum := hS u hu
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [kernel, abs_div, abs_of_pos hMr]
  calc
    |characterSum S u| / M ≤ (4 * Real.sqrt ((d : ℝ) * M)) / M :=
      div_le_div_of_nonneg_right hsum hMr.le
    _ = 4 * Real.sqrt ((d : ℝ) / M) := by
      have hdr : (0 : ℝ) ≤ d := by positivity
      have hsM : Real.sqrt (M : ℝ) ≠ 0 := (Real.sqrt_pos.2 hMr).ne'
      rw [Real.sqrt_mul hdr, Real.sqrt_div hdr]
      have hsquare : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = M := by
        nlinarith [Real.sq_sqrt hMr.le]
      have hdiv : Real.sqrt (M : ℝ) / M = 1 / Real.sqrt (M : ℝ) := by
        nth_rewrite 2 [← hsquare]
        field_simp
      calc
        4 * (Real.sqrt (d : ℝ) * Real.sqrt (M : ℝ)) / M =
            4 * Real.sqrt (d : ℝ) * (Real.sqrt (M : ℝ) / M) := by ring
        _ = 4 * Real.sqrt (d : ℝ) * (1 / Real.sqrt (M : ℝ)) := by rw [hdiv]
        _ = 4 * (Real.sqrt (d : ℝ) / Real.sqrt (M : ℝ)) := by ring

end

end PegSeparation.LowerBound.RandomCoherence
