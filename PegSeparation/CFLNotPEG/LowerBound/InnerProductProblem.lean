import PegSeparation.CFLNotPEG.LowerBound.ProtocolBridge


open scoped BigOperators

namespace PegSeparation.LowerBound.InnerProductProblem

open PegSeparation
open PegSeparation.LowerBound

noncomputable section

def querySign {M : ℕ} (outsideParity : Fin M → Bool) (q : Fin M) : ℝ :=
  if outsideParity q then -1 else 1

@[simp] theorem abs_querySign {M : ℕ} (outsideParity : Fin M → Bool)
    (q : Fin M) : |querySign outsideParity q| = 1 := by
  cases h : outsideParity q <;> simp [querySign, h]

@[simp] theorem querySign_sq {M : ℕ} (outsideParity : Fin M → Bool)
    (q : Fin M) : querySign outsideParity q ^ 2 = 1 := by
  simp [querySign]

def signedCharacter {d M : ℕ}
    (rows : RandomCoherence.RowMatrix d M)
    (outsideParity : Fin M → Bool)
    (q : Fin M) (input : RandomCoherence.F2Vec d) : ℝ :=
  querySign outsideParity q * RandomCoherence.chi rows q input

theorem signedCharacter_eq_neg_one_or_one {d M : ℕ}
    (rows : RandomCoherence.RowMatrix d M)
    (outsideParity : Fin M → Bool)
    (q : Fin M) (input : RandomCoherence.F2Vec d) :
    signedCharacter rows outsideParity q input = -1 ∨
      signedCharacter rows outsideParity q input = 1 := by
  rcases RandomCoherence.rowCharacter_eq_neg_one_or_one (rows q) input with
    hchi | hchi
  · by_cases hout : outsideParity q
    · right
      simp [signedCharacter, querySign, RandomCoherence.chi, hout, hchi]
    · left
      simp [signedCharacter, querySign, RandomCoherence.chi, hout, hchi]
  · by_cases hout : outsideParity q
    · left
      simp [signedCharacter, querySign, RandomCoherence.chi, hout, hchi]
    · right
      simp [signedCharacter, querySign, RandomCoherence.chi, hout, hchi]

def problem {d M : ℕ}
    (rows : RandomCoherence.RowMatrix d M)
    (outsideParity : Fin M → Bool) :
    BinaryProblem (RandomCoherence.F2Vec d) (Fin M) where
  value := fun q input => signedCharacter rows outsideParity q input < 0

theorem problem_character {d M : ℕ}
    (rows : RandomCoherence.RowMatrix d M)
    (outsideParity : Fin M → Bool)
    (q : Fin M) (input : RandomCoherence.F2Vec d) :
    (problem rows outsideParity).character q input =
      MessageBound.signedRows (querySign outsideParity)
        (RandomCoherence.chi rows) q input := by
  simp only [BinaryProblem.character, problem, MessageBound.signedRows]
  change
    (if decide (signedCharacter rows outsideParity q input < 0) = true
      then -1 else 1) =
      signedCharacter rows outsideParity q input
  rcases signedCharacter_eq_neg_one_or_one rows outsideParity q input with
    hneg | hpos
  · simp [hneg]
  · simp [hpos]

theorem problem_isBalanced {d M : ℕ}
    (rows : RandomCoherence.RowMatrix d M)
    (outsideParity : Fin M → Bool)
    (hrows : ∀ q, rows q ≠ 0) :
    (problem rows outsideParity).IsBalanced
      (ProtocolBridge.uniformFiniteDistribution (RandomCoherence.F2Vec d)) := by
  intro q
  rw [show (∑ input,
      (ProtocolBridge.uniformFiniteDistribution
        (RandomCoherence.F2Vec d)).mass input *
        (problem rows outsideParity).character q input) =
      querySign outsideParity q *
        ((∑ input, RandomCoherence.chi rows q input) /
          (Fintype.card (RandomCoherence.F2Vec d) : ℝ)) by
    simp_rw [ProtocolBridge.uniformFiniteDistribution_mass,
      problem_character, MessageBound.signedRows]
    calc
      (∑ input,
          1 / (Fintype.card (RandomCoherence.F2Vec d) : ℝ) *
            (querySign outsideParity q * RandomCoherence.chi rows q input)) =
          ∑ input,
            (querySign outsideParity q /
              (Fintype.card (RandomCoherence.F2Vec d) : ℝ)) *
              RandomCoherence.chi rows q input := by
            apply Finset.sum_congr rfl
            intro input _
            ring
      _ = (querySign outsideParity q /
            (Fintype.card (RandomCoherence.F2Vec d) : ℝ)) *
            ∑ input, RandomCoherence.chi rows q input := by
          rw [Finset.mul_sum]
      _ = querySign outsideParity q *
            ((∑ input, RandomCoherence.chi rows q input) /
              (Fintype.card (RandomCoherence.F2Vec d) : ℝ)) := by
          ring]
  rw [← Fintype.expect_eq_sum_div_card]
  rw [RandomCoherence.expect_chi_eq_zero d M rows q (hrows q)]
  simp

theorem protocolAdvantage_upper {d M messageBits coinCount : ℕ}
    [Nonempty (Fin M)]
    (rows : RandomCoherence.RowMatrix d M)
    (outsideParity : Fin M → Bool)
    (protocol : PublicCoinProtocol (RandomCoherence.F2Vec d)
      messageBits coinCount)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hcoherence : ∀ u : RandomCoherence.F2Vec d, u ≠ 0 →
      |RandomCoherence.kernel rows u| ≤ mu) :
    protocol.advantage (problem rows outsideParity)
        (ProtocolBridge.uniformFiniteDistribution (RandomCoherence.F2Vec d))
        (ProtocolBridge.uniformFiniteDistribution (Fin M)) ≤
      (2 : ℝ) ^ (((messageBits : ℝ) - (d : ℝ)) / 2) + √mu := by
  exact ProtocolBridge.publicCoinAdvantage_le_signedBinaryMatrix
    rows (querySign outsideParity) (problem rows outsideParity) protocol mu hmu
    (abs_querySign outsideParity)
    (problem_character rows outsideParity) hcoherence

end

end PegSeparation.LowerBound.InnerProductProblem
