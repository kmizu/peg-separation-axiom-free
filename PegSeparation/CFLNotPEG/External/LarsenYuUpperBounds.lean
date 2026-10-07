import PegSeparation.CFLNotPEG.External.Assumptions


open scoped BigOperators

namespace PegSeparation

namespace CellProbe.StaticStructure

variable {Input Query : Type} [Fintype Input] [Fintype Query]
  {wordBits cacheCells maxUpdatedCells : Nat}

theorem expectedTotalProbes_nonneg
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    0 ≤ dataStructure.expectedTotalProbes
      inputDistribution queryDistribution := by
  unfold expectedTotalProbes
  apply Finset.sum_nonneg
  intro input _
  apply mul_nonneg (inputDistribution.mass_nonnegative input)
  apply Finset.sum_nonneg
  intro query _
  exact mul_nonneg (queryDistribution.mass_nonnegative query) (Nat.cast_nonneg _)

theorem expectedUpdatedProbes_nonneg
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    0 ≤ dataStructure.expectedUpdatedProbes
      inputDistribution queryDistribution := by
  unfold expectedUpdatedProbes
  apply Finset.sum_nonneg
  intro input _
  apply mul_nonneg (inputDistribution.mass_nonnegative input)
  apply Finset.sum_nonneg
  intro query _
  exact mul_nonneg (queryDistribution.mass_nonnegative query) (Nat.cast_nonneg _)

end CellProbe.StaticStructure

theorem log₂_one_div_nonneg {p : ℝ} (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    0 ≤ log₂ (1 / p) := by
  have hpone : p ≤ 1 := by linarith
  have hinv : 1 ≤ 1 / p := by
    rw [le_div_iff₀ hp]
    linarith
  unfold log₂
  exact div_nonneg (Real.log_nonneg hinv) (Real.log_pos (by norm_num)).le

namespace InternalLowerBoundAssumptions

theorem larsenYuBetaOne_upperBounds
    (external : InternalLowerBoundAssumptions) :
    ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
      ∀ {Input Query : Type} [Fintype Input] [Fintype Query]
        {wordBits cacheCells maxUpdatedCells : Nat}
        (problem : BinaryProblem Input Query)
        (inputDistribution : FiniteDistribution Input)
        (queryDistribution : FiniteDistribution Query)
        (dataStructure : CellProbe.StaticStructure Input Query
          wordBits cacheCells maxUpdatedCells)
        (tTotal tUpdated p : ℝ),
        0 < wordBits →
        problem.IsBalanced inputDistribution →
        dataStructure.Solves problem →
        dataStructure.expectedTotalProbes inputDistribution queryDistribution ≤ tTotal →
        dataStructure.expectedUpdatedProbes inputDistribution queryDistribution ≤ tUpdated →
        0 < p → p ≤ (1 / 2 : ℝ) →
        ∃ (messageBits coinCount : Nat)
          (protocol : PublicCoinProtocol Input messageBits coinCount),
          (messageBits : ℝ) ≤
              (8 * p * (maxUpdatedCells : ℝ) + (cacheCells : ℝ)) *
                  (wordBits : ℝ) + 2 ∧
            Real.rpow 2
                (-A *
                  (Real.sqrt
                    (tTotal * (1 + tUpdated * log₂ (1 / p))) +
                    (1 + tUpdated * log₂ (1 / p))) *
                  log₂ (1 / p)) -
                Real.rpow 2 (-a * p * (maxUpdatedCells : ℝ)) ≤
              protocol.advantage problem inputDistribution queryDistribution := by
  obtain ⟨A, a, hA, ha, hexact⟩ := external.larsenYuBetaOne
  refine ⟨A, a, hA, ha, ?_⟩
  intro Input Query instInput instQuery wordBits cacheCells maxUpdatedCells
    problem inputDistribution queryDistribution dataStructure
    tTotal tUpdated p hword hbalanced hsolves htotal hupdated hp hhalf
  obtain ⟨messageBits, coinCount, protocol, hmessage, hadvantage⟩ :=
    hexact problem inputDistribution queryDistribution dataStructure p
      hword hbalanced hsolves hp hhalf
  refine ⟨messageBits, coinCount, protocol, le_of_lt hmessage, ?_⟩
  let actualTotal : ℝ :=
    dataStructure.expectedTotalProbes inputDistribution queryDistribution
  let actualUpdated : ℝ :=
    dataStructure.expectedUpdatedProbes inputDistribution queryDistribution
  let logInv : ℝ := log₂ (1 / p)
  let actualLambda : ℝ := 1 + actualUpdated * logInv
  let boundedLambda : ℝ := 1 + tUpdated * logInv
  have hactualTotal : 0 ≤ actualTotal := by
    exact dataStructure.expectedTotalProbes_nonneg
      inputDistribution queryDistribution
  have hactualUpdated : 0 ≤ actualUpdated := by
    exact dataStructure.expectedUpdatedProbes_nonneg
      inputDistribution queryDistribution
  have hlogInv : 0 ≤ logInv := by
    exact log₂_one_div_nonneg hp hhalf
  have htotal' : actualTotal ≤ tTotal := htotal
  have hupdated' : actualUpdated ≤ tUpdated := hupdated
  have hactualLambda : 0 ≤ actualLambda := by
    dsimp only [actualLambda]
    positivity
  have hboundedLambda : 0 ≤ boundedLambda := by
    have htUpdated : 0 ≤ tUpdated := hactualUpdated.trans hupdated'
    dsimp only [boundedLambda]
    positivity
  have hlambda : actualLambda ≤ boundedLambda := by
    dsimp only [actualLambda, boundedLambda]
    exact add_le_add_right (mul_le_mul_of_nonneg_right hupdated' hlogInv) 1
  have hproduct : actualTotal * actualLambda ≤ tTotal * boundedLambda := by
    exact mul_le_mul htotal' hlambda hactualLambda (hactualTotal.trans htotal')
  have hsqrt : Real.sqrt (actualTotal * actualLambda) ≤
      Real.sqrt (tTotal * boundedLambda) :=
    Real.sqrt_le_sqrt hproduct
  have hsum : Real.sqrt (actualTotal * actualLambda) + actualLambda ≤
      Real.sqrt (tTotal * boundedLambda) + boundedLambda :=
    add_le_add hsqrt hlambda
  have hscaled :
      A * (Real.sqrt (actualTotal * actualLambda) + actualLambda) * logInv ≤
        A * (Real.sqrt (tTotal * boundedLambda) + boundedLambda) * logInv := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsum hA.le) hlogInv
  have hexponent :
      -A * (Real.sqrt (tTotal * boundedLambda) + boundedLambda) * logInv ≤
        -A * (Real.sqrt (actualTotal * actualLambda) + actualLambda) * logInv := by
    nlinarith
  have hmain :
      Real.rpow 2
          (-A * (Real.sqrt (tTotal * boundedLambda) + boundedLambda) * logInv) ≤
        Real.rpow 2
          (-A * (Real.sqrt (actualTotal * actualLambda) + actualLambda) * logInv) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  dsimp only [actualTotal, actualUpdated, logInv, actualLambda, boundedLambda] at hmain
  exact (sub_le_sub_right hmain _).trans hadvantage

end InternalLowerBoundAssumptions

end PegSeparation
