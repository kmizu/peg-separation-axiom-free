import PegSeparation.CFLNotPEG.External.Assumptions


open scoped BigOperators

namespace PegSeparation.External.LarsenYuConditionalJensen

noncomputable section

theorem partitionL1_mono_of_factor
    {Input Coarse Fine : Type} [Fintype Input] [Fintype Coarse] [Fintype Fine]
    [DecidableEq Coarse] [DecidableEq Fine]
    (weight signal : Input → ℝ)
    (coarse : Input → Coarse) (fine : Input → Fine)
    (decode : Fine → Coarse)
    (hfactor : ∀ input, decode (fine input) = coarse input) :
    (∑ coarseMessage : Coarse,
        |∑ input : Input, weight input *
          (if coarse input = coarseMessage then signal input else 0)|) ≤
      ∑ fineMessage : Fine,
        |∑ input : Input, weight input *
          (if fine input = fineMessage then signal input else 0)| := by
  classical
  let contribution (fineMessage : Fine) : ℝ :=
    ∑ input : Input, weight input *
      (if fine input = fineMessage then signal input else 0)
  have hdecompose (coarseMessage : Coarse) :
      (∑ input : Input, weight input *
          (if coarse input = coarseMessage then signal input else 0)) =
        ∑ fineMessage : Fine,
          if decode fineMessage = coarseMessage then contribution fineMessage else 0 := by
    symm
    calc
      (∑ fineMessage : Fine,
          if decode fineMessage = coarseMessage then contribution fineMessage else 0) =
          ∑ fineMessage : Fine, ∑ input : Input,
            if fine input = fineMessage then
              (if decode fineMessage = coarseMessage then
                weight input * signal input else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro fineMessage _hfineMessage
        by_cases hdecode : decode fineMessage = coarseMessage
        · simp [hdecode, contribution, mul_ite]
        · simp [hdecode]
      _ = ∑ input : Input, ∑ fineMessage : Fine,
            if fine input = fineMessage then
              (if decode fineMessage = coarseMessage then
                weight input * signal input else 0) else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ input : Input, weight input *
          (if coarse input = coarseMessage then signal input else 0) := by
        apply Finset.sum_congr rfl
        intro input _hinput
        rw [← hfactor input]
        simp [mul_ite]
  calc
    (∑ coarseMessage : Coarse,
        |∑ input : Input, weight input *
          (if coarse input = coarseMessage then signal input else 0)|) =
        ∑ coarseMessage : Coarse,
          |∑ fineMessage : Fine,
            if decode fineMessage = coarseMessage then
              contribution fineMessage else 0| := by
      apply Finset.sum_congr rfl
      intro coarseMessage _hcoarseMessage
      rw [hdecompose]
    _ ≤ ∑ coarseMessage : Coarse, ∑ fineMessage : Fine,
          |if decode fineMessage = coarseMessage then
            contribution fineMessage else 0| := by
      apply Finset.sum_le_sum
      intro coarseMessage _hcoarseMessage
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ fineMessage : Fine,
          |∑ input : Input, weight input *
            (if fine input = fineMessage then signal input else 0)| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro fineMessage _hfineMessage
      rw [Fintype.sum_eq_single (decode fineMessage)]
      · simp [contribution]
      · intro other hne
        simp [hne.symm]

theorem publicCoinAdvantage_mono_of_factor
    {Input Query : Type} [Fintype Input] [Fintype Query]
    {coarseBits fineBits coinCount : Nat}
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (coarseProtocol : PublicCoinProtocol Input coarseBits coinCount)
    (fineProtocol : PublicCoinProtocol Input fineBits coinCount)
    (hcoins : fineProtocol.coinDistribution = coarseProtocol.coinDistribution)
    (decode : Fin coinCount → BitVec fineBits → BitVec coarseBits)
    (hfactor : ∀ coin input,
      decode coin (fineProtocol.encode coin input) =
        coarseProtocol.encode coin input) :
    coarseProtocol.advantage problem inputDistribution queryDistribution ≤
      fineProtocol.advantage problem inputDistribution queryDistribution := by
  classical
  unfold PublicCoinProtocol.advantage
  rw [hcoins]
  apply Finset.sum_le_sum
  intro coin _hcoin
  apply mul_le_mul_of_nonneg_left _
    (coarseProtocol.coinDistribution.mass_nonnegative coin)
  apply Finset.sum_le_sum
  intro query _hquery
  apply mul_le_mul_of_nonneg_left _
    (queryDistribution.mass_nonnegative query)
  exact partitionL1_mono_of_factor
    inputDistribution.mass (problem.character query)
    (coarseProtocol.encode coin) (fineProtocol.encode coin)
    (decode coin) (hfactor coin)

end

end PegSeparation.External.LarsenYuConditionalJensen
