import PegSeparation.CFLNotPEG.LowerBound.CoherenceFour
import PegSeparation.CFLNotPEG.LowerBound.InnerProductProblem


namespace PegSeparation.LowerBound.ProtocolEndgame

open PegSeparation
open PegSeparation.LowerBound

noncomputable section

lemma sqrt_four_mul_sqrt (x : ℝ) (hx : 0 ≤ x) :
    √(4 * √x) = 2 * x ^ (1 / 4 : ℝ) := by
  calc
    √(4 * √x) = √(4 : ℝ) * √(√x) :=
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) _
    _ = 2 * √(√x) := by norm_num
    _ = 2 * (√x) ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
    _ = 2 * (x ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    _ = 2 * x ^ ((1 / 2 : ℝ) * (1 / 2 : ℝ)) := by
      rw [← Real.rpow_mul hx]
    _ = 2 * x ^ (1 / 4 : ℝ) := by norm_num

theorem protocolAdvantage_upper_fourthRoot
    {d M messageBits coinCount : ℕ} [Nonempty (Fin M)]
    (rows : RandomCoherence.RowMatrix d M)
    (outsideParity : Fin M → Bool)
    (protocol : PublicCoinProtocol (RandomCoherence.F2Vec d)
      messageBits coinCount)
    (hM : 0 < M)
    (hmessage : (messageBits : ℝ) ≤ (d : ℝ) / 2)
    (hcoherence : ∀ u : RandomCoherence.F2Vec d, u ≠ 0 →
      |RandomCoherence.kernel rows u| ≤
        4 * Real.sqrt ((d : ℝ) / (M : ℝ))) :
    protocol.advantage (InnerProductProblem.problem rows outsideParity)
        (ProtocolBridge.uniformFiniteDistribution (RandomCoherence.F2Vec d))
        (ProtocolBridge.uniformFiniteDistribution (Fin M)) ≤
      (2 : ℝ) ^ (-(d : ℝ) / 4) +
        2 * ((d : ℝ) / (M : ℝ)) ^ (1 / 4 : ℝ) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hratio : 0 ≤ (d : ℝ) / (M : ℝ) :=
    div_nonneg (Nat.cast_nonneg d) hMr.le
  have hmu : 0 ≤ 4 * Real.sqrt ((d : ℝ) / (M : ℝ)) := by
    positivity
  have hraw := InnerProductProblem.protocolAdvantage_upper
    rows outsideParity protocol
    (4 * Real.sqrt ((d : ℝ) / (M : ℝ))) hmu hcoherence
  have hexponent :
      ((messageBits : ℝ) - (d : ℝ)) / 2 ≤ -(d : ℝ) / 4 := by
    linarith
  have hpow :
      (2 : ℝ) ^ (((messageBits : ℝ) - (d : ℝ)) / 2) ≤
        (2 : ℝ) ^ (-(d : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  calc
    protocol.advantage (InnerProductProblem.problem rows outsideParity)
        (ProtocolBridge.uniformFiniteDistribution (RandomCoherence.F2Vec d))
        (ProtocolBridge.uniformFiniteDistribution (Fin M)) ≤
        (2 : ℝ) ^ (((messageBits : ℝ) - (d : ℝ)) / 2) +
          √(4 * Real.sqrt ((d : ℝ) / (M : ℝ))) := hraw
    _ ≤ (2 : ℝ) ^ (-(d : ℝ) / 4) +
          √(4 * Real.sqrt ((d : ℝ) / (M : ℝ))) :=
      add_le_add hpow (le_refl _)
    _ = (2 : ℝ) ^ (-(d : ℝ) / 4) +
          2 * ((d : ℝ) / (M : ℝ)) ^ (1 / 4 : ℝ) := by
      rw [sqrt_four_mul_sqrt _ hratio]

theorem balanced_and_protocolAdvantage_upper_fourthRoot
    {d M messageBits coinCount : ℕ} [Nonempty (Fin M)]
    (rows : RandomCoherence.RowMatrix d M)
    (outsideParity : Fin M → Bool)
    (protocol : PublicCoinProtocol (RandomCoherence.F2Vec d)
      messageBits coinCount)
    (hM : 0 < M)
    (hrows : ∀ q, rows q ≠ 0)
    (hmessage : (messageBits : ℝ) ≤ (d : ℝ) / 2)
    (hcoherence : ∀ u : RandomCoherence.F2Vec d, u ≠ 0 →
      |RandomCoherence.kernel rows u| ≤
        4 * Real.sqrt ((d : ℝ) / (M : ℝ))) :
    (InnerProductProblem.problem rows outsideParity).IsBalanced
        (ProtocolBridge.uniformFiniteDistribution (RandomCoherence.F2Vec d)) ∧
      protocol.advantage (InnerProductProblem.problem rows outsideParity)
          (ProtocolBridge.uniformFiniteDistribution (RandomCoherence.F2Vec d))
          (ProtocolBridge.uniformFiniteDistribution (Fin M)) ≤
        (2 : ℝ) ^ (-(d : ℝ) / 4) +
          2 * ((d : ℝ) / (M : ℝ)) ^ (1 / 4 : ℝ) := by
  exact ⟨InnerProductProblem.problem_isBalanced rows outsideParity hrows,
    protocolAdvantage_upper_fourthRoot rows outsideParity protocol hM
      hmessage hcoherence⟩

theorem exists_matrix_balanced_and_protocolAdvantage_upper_fourthRoot
    {d M messageBits coinCount : ℕ} [Nonempty (Fin M)]
    (hd : 2 ≤ d) (hM : 0 < M)
    (hzero : (M : ℝ) / (2 : ℝ) ^ d < 1 / 8)
    (outsideParity : Fin M → Bool)
    (protocol : PublicCoinProtocol (RandomCoherence.F2Vec d)
      messageBits coinCount)
    (hmessage : (messageBits : ℝ) ≤ (d : ℝ) / 2) :
    ∃ rows : RandomCoherence.RowMatrix d M,
      (∀ q, rows q ≠ 0) ∧
      (InnerProductProblem.problem rows outsideParity).IsBalanced
          (ProtocolBridge.uniformFiniteDistribution (RandomCoherence.F2Vec d)) ∧
      protocol.advantage (InnerProductProblem.problem rows outsideParity)
          (ProtocolBridge.uniformFiniteDistribution (RandomCoherence.F2Vec d))
          (ProtocolBridge.uniformFiniteDistribution (Fin M)) ≤
        (2 : ℝ) ^ (-(d : ℝ) / 4) +
          2 * ((d : ℝ) / (M : ℝ)) ^ (1 / 4 : ℝ) := by
  obtain ⟨rows, hrows, hcoherence⟩ :=
    RandomCoherence.exists_matrix_no_zero_row_kernel_le_four_sqrt
      d M hd hM hzero
  refine ⟨rows, hrows, ?_, ?_⟩
  · exact InnerProductProblem.problem_isBalanced rows outsideParity hrows
  · exact protocolAdvantage_upper_fourthRoot rows outsideParity protocol hM
      hmessage hcoherence

end

end PegSeparation.LowerBound.ProtocolEndgame
