import PegSeparation.CFLNotPEG.External.Assumptions
import PegSeparation.CFLNotPEG.LowerBound.MessageBound
import PegSeparation.CFLNotPEG.LowerBound.RandomCoherence


open scoped BigOperators

namespace PegSeparation.LowerBound.ProtocolBridge

noncomputable section


def uniformFiniteDistribution (X : Type) [Fintype X] [Nonempty X] :
    FiniteDistribution X where
  mass := fun _ ↦ 1 / (Fintype.card X : ℝ)
  mass_nonnegative := fun _ ↦ by positivity
  mass_sum := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card X : ℝ) ≠ 0 := by positivity
    field_simp

@[simp]
theorem uniformFiniteDistribution_mass (X : Type) [Fintype X] [Nonempty X]
    (x : X) :
    (uniformFiniteDistribution X).mass x = 1 / (Fintype.card X : ℝ) :=
  rfl

def fixedSeedEncoder {Input : Type} {messageBits coinCount : ℕ}
    (protocol : PublicCoinProtocol Input messageBits coinCount)
    (coin : Fin coinCount) (input : Input) (message : BitVec messageBits) : ℝ :=
  if protocol.encode coin input = message then 1 else 0

@[simp]
theorem fixedSeedEncoder_nonnegative {Input : Type} {messageBits coinCount : ℕ}
    (protocol : PublicCoinProtocol Input messageBits coinCount)
    (coin : Fin coinCount) (input : Input) (message : BitVec messageBits) :
    0 ≤ fixedSeedEncoder protocol coin input message := by
  simp only [fixedSeedEncoder]
  split <;> norm_num

@[simp]
theorem fixedSeedEncoder_row_sum {Input : Type} {messageBits coinCount : ℕ}
    (protocol : PublicCoinProtocol Input messageBits coinCount)
    (coin : Fin coinCount) (input : Input) :
    ∑ message : BitVec messageBits, fixedSeedEncoder protocol coin input message = 1 := by
  classical
  simp [fixedSeedEncoder]

def posteriorCharacterSum {Input Query : Type} [Fintype Input]
    {messageBits coinCount : ℕ}
    (protocol : PublicCoinProtocol Input messageBits coinCount)
    (problem : BinaryProblem Input Query) (coin : Fin coinCount)
    (query : Query) (message : BitVec messageBits) : ℝ :=
  ∑ input, fixedSeedEncoder protocol coin input message *
    problem.character query input

def fixedSeedDecoder {Input Query : Type} [Fintype Input]
    {messageBits coinCount : ℕ}
    (protocol : PublicCoinProtocol Input messageBits coinCount)
    (problem : BinaryProblem Input Query) (coin : Fin coinCount)
    (query : Query) (message : BitVec messageBits) : Bool :=
  if posteriorCharacterSum protocol problem coin query message < 0 then true else false

theorem fixedSeedDecoder_is_optimal {Input Query : Type} [Fintype Input]
    {messageBits coinCount : ℕ}
    (protocol : PublicCoinProtocol Input messageBits coinCount)
    (problem : BinaryProblem Input Query) (coin : Fin coinCount)
    (query : Query) (message : BitVec messageBits) :
    (if fixedSeedDecoder protocol problem coin query message then (-1 : ℝ) else 1) *
        posteriorCharacterSum protocol problem coin query message =
      |posteriorCharacterSum protocol problem coin query message| := by
  unfold fixedSeedDecoder
  by_cases h : posteriorCharacterSum protocol problem coin query message < 0
  · simp [h, abs_of_neg h]
  · have hnonnegative :
        0 ≤ posteriorCharacterSum protocol problem coin query message := le_of_not_gt h
    simp [h, abs_of_nonneg hnonnegative]


theorem fixedSeedAdvantage_eq_messageBound
    {Input Query : Type} [Fintype Input] [Fintype Query]
    [Nonempty Input] [Nonempty Query]
    {messageBits coinCount : ℕ}
    (protocol : PublicCoinProtocol Input messageBits coinCount)
    (problem : BinaryProblem Input Query) (coin : Fin coinCount) :
    (∑ query, (uniformFiniteDistribution Query).mass query *
      ∑ message : BitVec messageBits,
        |∑ input, (uniformFiniteDistribution Input).mass input *
          (if protocol.encode coin input = message then
            problem.character query input else 0)|) =
      MessageBound.advantage (fixedSeedEncoder protocol coin) problem.character := by
  classical
  let CI : ℝ := Fintype.card Input
  have hCI : 0 < CI := by simp only [CI]; positivity
  unfold MessageBound.advantage
  simp only [uniformFiniteDistribution_mass]
  have hinner (query : Query) (message : BitVec messageBits) :
      (∑ input, (1 / (Fintype.card Input : ℝ)) *
          (if protocol.encode coin input = message then
            problem.character query input else 0)) =
        (1 / CI) *
          (∑ input, fixedSeedEncoder protocol coin input message *
            problem.character query input) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro input _
    simp only [CI, fixedSeedEncoder]
    split <;> ring
  simp_rw [hinner]
  have habsCI : |1 / CI| = (1 / CI : ℝ) :=
    abs_of_pos (one_div_pos.mpr hCI)
  simp_rw [abs_mul, habsCI]
  simp only [CI]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro message _
  rw [Finset.sum_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro query _
  ring

theorem publicCoinAdvantage_eq_weighted_messageBound
    {Input Query : Type} [Fintype Input] [Fintype Query]
    [Nonempty Input] [Nonempty Query]
    {messageBits coinCount : ℕ}
    (protocol : PublicCoinProtocol Input messageBits coinCount)
    (problem : BinaryProblem Input Query) :
    protocol.advantage problem (uniformFiniteDistribution Input)
        (uniformFiniteDistribution Query) =
      ∑ coin, protocol.coinDistribution.mass coin *
        MessageBound.advantage (fixedSeedEncoder protocol coin) problem.character := by
  unfold PublicCoinProtocol.advantage
  apply Finset.sum_congr rfl
  intro coin _
  rw [fixedSeedAdvantage_eq_messageBound protocol problem coin]


theorem publicCoinAdvantage_le_bits
    {Input Query : Type} [Fintype Input] [Fintype Query]
    [Nonempty Input] [Nonempty Query]
    {messageBits coinCount d : ℕ}
    (protocol : PublicCoinProtocol Input messageBits coinCount)
    (problem : BinaryProblem Input Query) (mu : ℝ)
    (hmu : 0 ≤ mu)
    (hdiag : ∀ input, MessageBound.kernel problem.character input input ≤ 1)
    (hoff : ∀ input input', input ≠ input' →
      |MessageBound.kernel problem.character input input'| ≤ mu)
    (hInputCard : Fintype.card Input = 2 ^ d) :
    protocol.advantage problem (uniformFiniteDistribution Input)
        (uniformFiniteDistribution Query) ≤
      (2 : ℝ) ^ (((messageBits : ℝ) - (d : ℝ)) / 2) + √mu := by
  classical
  rw [publicCoinAdvantage_eq_weighted_messageBound protocol problem]
  let bound : ℝ :=
    (2 : ℝ) ^ (((messageBits : ℝ) - (d : ℝ)) / 2) + √mu
  calc
    (∑ coin, protocol.coinDistribution.mass coin *
        MessageBound.advantage (fixedSeedEncoder protocol coin) problem.character) ≤
        ∑ coin, protocol.coinDistribution.mass coin * bound := by
      apply Finset.sum_le_sum
      intro coin _
      apply mul_le_mul_of_nonneg_left _
        (protocol.coinDistribution.mass_nonnegative coin)
      exact MessageBound.advantage_le_bits problem.character
        (fixedSeedEncoder protocol coin) mu messageBits d hmu
        (fun input message ↦ fixedSeedEncoder_nonnegative protocol coin input message)
        (fun input ↦ fixedSeedEncoder_row_sum protocol coin input)
        hdiag hoff hInputCard (by
          rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec])
    _ = bound := by
      rw [← Finset.sum_mul, protocol.coinDistribution.mass_sum, one_mul]
    _ = (2 : ℝ) ^ (((messageBits : ℝ) - (d : ℝ)) / 2) + √mu := rfl


theorem messageKernel_chi_eq {d M : ℕ} (S : RandomCoherence.RowMatrix d M)
    (y y' : RandomCoherence.F2Vec d) :
    MessageBound.kernel (RandomCoherence.chi S) y y' =
      RandomCoherence.kernel S (y + y') := by
  unfold MessageBound.kernel
  rw [RandomCoherence.kernel_eq_average_chi]
  simp only [Fintype.card_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  change RandomCoherence.rowCharacter (S q) y *
      RandomCoherence.rowCharacter (S q) y' =
    RandomCoherence.rowCharacter (S q) (y + y')
  exact (AddChar.map_add_eq_mul (RandomCoherence.rowCharacter (S q)) y y').symm

theorem messageKernel_chi_diag {d M : ℕ} (S : RandomCoherence.RowMatrix d M)
    (hM : 0 < M) (y : RandomCoherence.F2Vec d) :
    MessageBound.kernel (RandomCoherence.chi S) y y = 1 := by
  rw [messageKernel_chi_eq]
  have hzero : y + y = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (y i)
  rw [hzero]
  simp [RandomCoherence.kernel, RandomCoherence.characterSum, hM.ne']

theorem messageKernel_chi_offdiag {d M : ℕ}
    (S : RandomCoherence.RowMatrix d M)
    (mu : ℝ)
    (hcoherence : ∀ u : RandomCoherence.F2Vec d, u ≠ 0 →
      |RandomCoherence.kernel S u| ≤ mu)
    (y y' : RandomCoherence.F2Vec d) (hne : y ≠ y') :
    |MessageBound.kernel (RandomCoherence.chi S) y y'| ≤ mu := by
  rw [messageKernel_chi_eq]
  apply hcoherence
  intro hzero
  apply hne
  funext i
  exact CharTwo.add_eq_zero.mp (congrFun hzero i)

theorem publicCoinAdvantage_le_binaryMatrix
    {d M messageBits coinCount : ℕ} [Nonempty (Fin M)]
    (S : RandomCoherence.RowMatrix d M)
    (problem : BinaryProblem (RandomCoherence.F2Vec d) (Fin M))
    (protocol : PublicCoinProtocol (RandomCoherence.F2Vec d) messageBits coinCount)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hcharacter : ∀ q y, problem.character q y = RandomCoherence.chi S q y)
    (hcoherence : ∀ u : RandomCoherence.F2Vec d, u ≠ 0 →
      |RandomCoherence.kernel S u| ≤ mu) :
    protocol.advantage problem (uniformFiniteDistribution (RandomCoherence.F2Vec d))
        (uniformFiniteDistribution (Fin M)) ≤
      (2 : ℝ) ^ (((messageBits : ℝ) - (d : ℝ)) / 2) + √mu := by
  have hM : 0 < M := Fin.pos_iff_nonempty.mpr inferInstance
  have htable : problem.character = RandomCoherence.chi S := by
    funext q y
    exact hcharacter q y
  apply publicCoinAdvantage_le_bits protocol problem mu hmu
  · rw [htable]
    intro y
    rw [messageKernel_chi_diag S hM y]
  · rw [htable]
    exact messageKernel_chi_offdiag S mu hcoherence
  · exact RandomCoherence.card_f2Vec d

theorem publicCoinAdvantage_le_signedBinaryMatrix
    {d M messageBits coinCount : ℕ} [Nonempty (Fin M)]
    (S : RandomCoherence.RowMatrix d M)
    (alpha : Fin M → ℝ)
    (problem : BinaryProblem (RandomCoherence.F2Vec d) (Fin M))
    (protocol : PublicCoinProtocol (RandomCoherence.F2Vec d) messageBits coinCount)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (halpha : ∀ q, |alpha q| = 1)
    (hcharacter : ∀ q y, problem.character q y =
      MessageBound.signedRows alpha (RandomCoherence.chi S) q y)
    (hcoherence : ∀ u : RandomCoherence.F2Vec d, u ≠ 0 →
      |RandomCoherence.kernel S u| ≤ mu) :
    protocol.advantage problem (uniformFiniteDistribution (RandomCoherence.F2Vec d))
        (uniformFiniteDistribution (Fin M)) ≤
      (2 : ℝ) ^ (((messageBits : ℝ) - (d : ℝ)) / 2) + √mu := by
  have hM : 0 < M := Fin.pos_iff_nonempty.mpr inferInstance
  have htable : problem.character =
      MessageBound.signedRows alpha (RandomCoherence.chi S) := by
    funext q y
    exact hcharacter q y
  have halphaSq : ∀ q, alpha q ^ 2 = 1 := by
    intro q
    calc
      alpha q ^ 2 = |alpha q| ^ 2 := (sq_abs (alpha q)).symm
      _ = 1 := by rw [halpha q]; norm_num
  apply publicCoinAdvantage_le_bits protocol problem mu hmu
  · rw [htable]
    intro y
    rw [MessageBound.kernel_signedRows alpha
      (RandomCoherence.chi S) halphaSq]
    exact (messageKernel_chi_diag S hM _).le
  · intro y y' hne
    rw [htable, MessageBound.kernel_signedRows alpha
      (RandomCoherence.chi S) halphaSq]
    exact messageKernel_chi_offdiag S mu hcoherence y y' hne
  · exact RandomCoherence.card_f2Vec d

end

end PegSeparation.LowerBound.ProtocolBridge
