import PegSeparation.CFLNotPEG.External.LarsenYuCappedAdvantage


open scoped BigOperators

namespace PegSeparation.External.LarsenYuCappedOutcome

noncomputable section

open LarsenYuBernoulli LarsenYuCappedAdvantage LarsenYuCappedCodec
  LarsenYuCappedRecovery LarsenYuCoinTransport LarsenYuExperimentAdvantage
  LarsenYuMessageCodecBounds LarsenYuPairOverflow
  LarsenYuPayloadCardinality
  LarsenYuCappedAdvantage.CellProbe.StaticStructure
  LarsenYuCappedCodec.CellProbe.StaticStructure
  LarsenYuCappedRecovery.CellProbe.StaticStructure
  LarsenYuExperimentAdvantage.CellProbe.StaticStructure
  LarsenYuPairOverflow.CellProbe.StaticStructure

namespace CellProbe.StaticStructure

variable {Input Query : Type} [Fintype Input] [Fintype Query]
  {wordBits cacheCells maxUpdatedCells : Nat}

theorem outcomeStructuredAdvantage_sub_quarter_rpow_le_cappedEncode
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (heffective : ∀ input address,
      address ∈ dataStructure.updatedAddresses input →
        dataStructure.updatedWord input address ≠
          dataStructure.preMemory address)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (hlarge : 4 ≤ p * (maxUpdatedCells : ℝ)) :
    outcomeStructuredAdvantage
        (pairMaskDistribution (wordBits := wordBits) p hp hpone)
        (experimentEncode dataStructure) problem inputDistribution
          queryDistribution -
      Real.rpow 2 (-(1 / 4 : ℝ) * p * maxUpdatedCells) ≤
    outcomeStructuredAdvantage
        (pairMaskDistribution (wordBits := wordBits) p hp hpone)
        (cappedEncode dataStructure p) problem inputDistribution
          queryDistribution := by
  classical
  let coinDistribution :=
    pairMaskDistribution (wordBits := wordBits) p hp hpone
  let originalPart := fun
      (coin : Mask (CellProbe.Address wordBits) ×
        Mask (CellProbe.Address wordBits)) (query : Query) ↦
    ∑ message : ExperimentMessage wordBits cacheCells,
      |∑ input, inputDistribution.mass input *
        (if experimentEncode dataStructure coin input = message
          then problem.character query input else 0)|
  let cappedPart := fun
      (coin : Mask (CellProbe.Address wordBits) ×
        Mask (CellProbe.Address wordBits)) (query : Query) ↦
    ∑ message : FixedPayload wordBits cacheCells
        (sampleCap p maxUpdatedCells),
      |∑ input, inputDistribution.mass input *
        (if cappedEncode dataStructure p coin input = message
          then problem.character query input else 0)|
  let overflowPart := fun
      (coin : Mask (CellProbe.Address wordBits) ×
        Mask (CellProbe.Address wordBits)) ↦
    ∑ input, inputDistribution.mass input *
      if pairOverflow dataStructure p coin input then 1 else 0
  have hsignal : ∀ query input,
      |problem.character query input| ≤ 1 := by
    intro query input
    unfold BinaryProblem.character
    split <;> simp
  have hpointwise : ∀ coin query,
      originalPart coin query ≤ cappedPart coin query + overflowPart coin := by
    intro coin query
    have hrecover :=
      experimentPartitionL1_sub_pairOverflowMass_le_cappedEncode
        dataStructure heffective p coin hlarge inputDistribution.mass
        (problem.character query) inputDistribution.mass_nonnegative
        (hsignal query)
    dsimp only [originalPart, cappedPart, overflowPart]
    linarith
  have hquery : ∀ coin,
      (∑ query, queryDistribution.mass query * originalPart coin query) ≤
        (∑ query, queryDistribution.mass query * cappedPart coin query) +
          overflowPart coin := by
    intro coin
    calc
      (∑ query, queryDistribution.mass query * originalPart coin query) ≤
          ∑ query, queryDistribution.mass query *
            (cappedPart coin query + overflowPart coin) := by
        apply Finset.sum_le_sum
        intro query _hquery
        exact mul_le_mul_of_nonneg_left (hpointwise coin query)
          (queryDistribution.mass_nonnegative query)
      _ = (∑ query, queryDistribution.mass query * cappedPart coin query) +
          overflowPart coin := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, queryDistribution.mass_sum, one_mul]
  have havg :
      (∑ coin, coinDistribution.mass coin *
        ∑ query, queryDistribution.mass query * originalPart coin query) ≤
      (∑ coin, coinDistribution.mass coin *
        ∑ query, queryDistribution.mass query * cappedPart coin query) +
      ∑ coin, coinDistribution.mass coin * overflowPart coin := by
    calc
      (∑ coin, coinDistribution.mass coin *
        ∑ query, queryDistribution.mass query * originalPart coin query) ≤
          ∑ coin, coinDistribution.mass coin *
            ((∑ query, queryDistribution.mass query * cappedPart coin query) +
              overflowPart coin) := by
        apply Finset.sum_le_sum
        intro coin _hcoin
        exact mul_le_mul_of_nonneg_left (hquery coin)
          (coinDistribution.mass_nonnegative coin)
      _ = (∑ coin, coinDistribution.mass coin *
          ∑ query, queryDistribution.mass query * cappedPart coin query) +
          ∑ coin, coinDistribution.mass coin * overflowPart coin := by
        simp_rw [mul_add, Finset.sum_add_distrib]
  have hoverflow :
      (∑ coin, coinDistribution.mass coin * overflowPart coin) ≤
        Real.rpow 2 (-(1 / 4 : ℝ) * p * maxUpdatedCells) := by
    dsimp only [coinDistribution, overflowPart]
    exact averagedPairOverflowMass_le_quarter_rpow dataStructure
      inputDistribution p hp hpone hlarge
  change
    (∑ coin, coinDistribution.mass coin *
      ∑ query, queryDistribution.mass query * originalPart coin query) -
        Real.rpow 2 (-(1 / 4 : ℝ) * p * maxUpdatedCells) ≤
      ∑ coin, coinDistribution.mass coin *
        ∑ query, queryDistribution.mass query * cappedPart coin query
  linarith

theorem card_fixedPayload_le_fixedMessageBits
    (p : ℝ) (maxUpdatedCells cacheCells wordBits : Nat) :
    Fintype.card
        (FixedPayload wordBits cacheCells (sampleCap p maxUpdatedCells)) ≤
      2 ^ fixedMessageBits p maxUpdatedCells cacheCells wordBits := by
  rw [card_fixedPayload]
  exact le_rfl

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuCappedOutcome
