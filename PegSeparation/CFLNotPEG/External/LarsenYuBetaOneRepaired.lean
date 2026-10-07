import PegSeparation.CFLNotPEG.External.LarsenYuUpperBounds


open scoped BigOperators

namespace PegSeparation.External.LarsenYuBetaOneRepaired

noncomputable section


def unitCoinDistribution : FiniteDistribution (Fin 1) where
  mass := fun _ ↦ 1
  mass_nonnegative := fun _ ↦ by norm_num
  mass_sum := by simp

def zeroMessageProtocol (Input : Type) : PublicCoinProtocol Input 0 1 where
  coinDistribution := unitCoinDistribution
  encode := fun _ _ ↦ 0

theorem zeroMessageProtocol_advantage_eq_zero
    {Input Query : Type} [Fintype Input] [Fintype Query]
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (hbalanced : problem.IsBalanced inputDistribution) :
    (zeroMessageProtocol Input).advantage problem inputDistribution
        queryDistribution = 0 := by
  classical
  unfold PublicCoinProtocol.advantage
  simp only [zeroMessageProtocol, unitCoinDistribution, Fin.sum_univ_one, one_mul]
  apply Finset.sum_eq_zero
  intro query _hquery
  have hmessages (message : BitVec 0) : message = 0 := Subsingleton.elim _ _
  simp_rw [hmessages]
  simp [hbalanced query]

theorem one_le_log₂_one_div {p : ℝ} (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    1 ≤ log₂ (1 / p) := by
  have hinv : (2 : ℝ) ≤ 1 / p := by
    rw [le_div_iff₀ hp]
    linarith
  have hlog : Real.log 2 ≤ Real.log (1 / p) :=
    Real.log_le_log (by norm_num) hinv
  unfold log₂
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  simpa using hlog

theorem one_le_lambda
    {Input Query : Type} [Fintype Input] [Fintype Query]
    {wordBits cacheCells maxUpdatedCells : Nat}
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    {p : ℝ} (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    1 ≤ 1 + dataStructure.expectedUpdatedProbes
      inputDistribution queryDistribution * log₂ (1 / p) := by
  have hupdated := dataStructure.expectedUpdatedProbes_nonneg
    inputDistribution queryDistribution
  have hlog := log₂_one_div_nonneg hp hhalf
  nlinarith

theorem one_le_correctedExponentFactor
    {Input Query : Type} [Fintype Input] [Fintype Query]
    {wordBits cacheCells maxUpdatedCells : Nat}
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    {p : ℝ} (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    1 ≤
      (Real.sqrt
          (dataStructure.expectedTotalProbes inputDistribution queryDistribution *
            (1 + dataStructure.expectedUpdatedProbes
              inputDistribution queryDistribution * log₂ (1 / p))) +
        (1 + dataStructure.expectedUpdatedProbes
          inputDistribution queryDistribution * log₂ (1 / p))) *
        log₂ (1 / p) := by
  let lambda : ℝ := 1 + dataStructure.expectedUpdatedProbes
    inputDistribution queryDistribution * log₂ (1 / p)
  have hlambda : 1 ≤ lambda := by
    exact one_le_lambda dataStructure inputDistribution queryDistribution hp hhalf
  have hsqrt : 0 ≤ Real.sqrt
      (dataStructure.expectedTotalProbes inputDistribution queryDistribution * lambda) :=
    Real.sqrt_nonneg _
  have hlog : 1 ≤ log₂ (1 / p) := one_le_log₂_one_div hp hhalf
  change 1 ≤ (Real.sqrt
    (dataStructure.expectedTotalProbes inputDistribution queryDistribution * lambda) +
      lambda) * log₂ (1 / p)
  nlinarith

theorem mainTerm_sub_error_nonpos_of_small
    {Input Query : Type} [Fintype Input] [Fintype Query]
    {wordBits cacheCells maxUpdatedCells : Nat}
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    {A a p : ℝ} (hA : 0 < A) (ha : 0 < a) (hAa : 4 * a ≤ A)
    (hp : 0 < p) (hhalf : p ≤ 1 / 2)
    (hsmall : p * (maxUpdatedCells : ℝ) ≤ 4) :
    Real.rpow 2
          (-A *
            (Real.sqrt
                (dataStructure.expectedTotalProbes inputDistribution queryDistribution *
                  (1 + dataStructure.expectedUpdatedProbes
                    inputDistribution queryDistribution * log₂ (1 / p))) +
              (1 + dataStructure.expectedUpdatedProbes
                inputDistribution queryDistribution * log₂ (1 / p))) *
            log₂ (1 / p)) -
        Real.rpow 2 (-a * p * (maxUpdatedCells : ℝ)) ≤ 0 := by
  let exponentFactor : ℝ :=
    (Real.sqrt
        (dataStructure.expectedTotalProbes inputDistribution queryDistribution *
          (1 + dataStructure.expectedUpdatedProbes
            inputDistribution queryDistribution * log₂ (1 / p))) +
      (1 + dataStructure.expectedUpdatedProbes
        inputDistribution queryDistribution * log₂ (1 / p))) *
      log₂ (1 / p)
  have hfactor : 1 ≤ exponentFactor := by
    exact one_le_correctedExponentFactor dataStructure inputDistribution
      queryDistribution hp hhalf
  have hexponent : -A * exponentFactor ≤
      -a * p * (maxUpdatedCells : ℝ) := by
    have haS : a * (p * (maxUpdatedCells : ℝ)) ≤ a * 4 :=
      mul_le_mul_of_nonneg_left hsmall ha.le
    have hA_factor : A ≤ A * exponentFactor := by nlinarith
    nlinarith
  have hrpow : Real.rpow 2 (-A * exponentFactor) ≤
      Real.rpow 2 (-a * p * (maxUpdatedCells : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  simpa [exponentFactor, mul_assoc] using sub_nonpos.mpr hrpow

theorem exists_protocol_smallRegime
    {Input Query : Type} [Fintype Input] [Fintype Query]
    {wordBits cacheCells maxUpdatedCells : Nat}
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (A a p : ℝ)
    (hA : 0 < A) (ha : 0 < a) (hAa : 4 * a ≤ A)
    (hbalanced : problem.IsBalanced inputDistribution)
    (hp : 0 < p) (hhalf : p ≤ (1 / 2 : ℝ))
    (hsmall : p * (maxUpdatedCells : ℝ) ≤ 4) :
    ∃ (messageBits coinCount : Nat)
      (protocol : PublicCoinProtocol Input messageBits coinCount),
      (messageBits : ℝ) <
          (8 * p * (maxUpdatedCells : ℝ) + (cacheCells : ℝ)) *
              (wordBits : ℝ) + 2 ∧
        Real.rpow 2
            (-A *
              (Real.sqrt
                (dataStructure.expectedTotalProbes inputDistribution queryDistribution *
                  (1 + dataStructure.expectedUpdatedProbes
                    inputDistribution queryDistribution * log₂ (1 / p))) +
                (1 + dataStructure.expectedUpdatedProbes
                  inputDistribution queryDistribution * log₂ (1 / p))) *
              log₂ (1 / p)) -
            Real.rpow 2 (-a * p * (maxUpdatedCells : ℝ)) ≤
          protocol.advantage problem inputDistribution queryDistribution := by
  refine ⟨0, 1, zeroMessageProtocol Input, ?_, ?_⟩
  · have hpS : 0 ≤ p * (maxUpdatedCells : ℝ) := by positivity
    have hcache : 0 ≤ (cacheCells : ℝ) := by positivity
    have hword : 0 ≤ (wordBits : ℝ) := by positivity
    have hcoefficient : 0 ≤
        8 * p * (maxUpdatedCells : ℝ) + (cacheCells : ℝ) := by
      nlinarith
    have hproduct : 0 ≤
        (8 * p * (maxUpdatedCells : ℝ) + (cacheCells : ℝ)) *
          (wordBits : ℝ) := mul_nonneg hcoefficient hword
    norm_num
    linarith
  · rw [zeroMessageProtocol_advantage_eq_zero problem inputDistribution
      queryDistribution hbalanced]
    exact mainTerm_sub_error_nonpos_of_small dataStructure inputDistribution
      queryDistribution hA ha hAa hp hhalf hsmall


def LarsenYuLargeRegimeAt (A a : ℝ) : Prop :=
  ∀ {Input Query : Type} [Fintype Input] [Fintype Query]
    {wordBits cacheCells maxUpdatedCells : Nat}
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (p : ℝ),
    0 < wordBits →
    problem.IsBalanced inputDistribution →
    dataStructure.Solves problem →
    0 < p → p ≤ (1 / 2 : ℝ) →
    4 ≤ p * (maxUpdatedCells : ℝ) →
    ∃ (messageBits coinCount : Nat)
      (protocol : PublicCoinProtocol Input messageBits coinCount),
      (messageBits : ℝ) <
          (8 * p * (maxUpdatedCells : ℝ) + (cacheCells : ℝ)) *
              (wordBits : ℝ) + 2 ∧
        Real.rpow 2
            (-A *
              (Real.sqrt
                (dataStructure.expectedTotalProbes inputDistribution queryDistribution *
                  (1 + dataStructure.expectedUpdatedProbes
                    inputDistribution queryDistribution * log₂ (1 / p))) +
                (1 + dataStructure.expectedUpdatedProbes
                  inputDistribution queryDistribution * log₂ (1 / p))) *
              log₂ (1 / p)) -
            Real.rpow 2 (-a * p * (maxUpdatedCells : ℝ)) ≤
          protocol.advantage problem inputDistribution queryDistribution

theorem larsenYuBetaOneExact_of_largeRegime
    {A a : ℝ} (hA : 0 < A) (ha : 0 < a) (hAa : 4 * a ≤ A)
    (hlarge : LarsenYuLargeRegimeAt A a) :
    LarsenYuBetaOneExactStatement := by
  refine ⟨A, a, hA, ha, ?_⟩
  intro Input Query instInput instQuery wordBits cacheCells maxUpdatedCells
    problem inputDistribution queryDistribution dataStructure p hword hbalanced
    hsolves hp hhalf
  by_cases hsmall : p * (maxUpdatedCells : ℝ) ≤ 4
  · exact exists_protocol_smallRegime problem inputDistribution queryDistribution
      dataStructure A a p hA ha hAa hbalanced hp hhalf hsmall
  · exact hlarge problem inputDistribution queryDistribution dataStructure p
      hword hbalanced hsolves hp hhalf (le_of_not_ge hsmall)

end

end PegSeparation.External.LarsenYuBetaOneRepaired
