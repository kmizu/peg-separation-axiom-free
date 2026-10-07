import PegSeparation.CFLNotPEG.External.LarsenYuCappedRecovery
import PegSeparation.CFLNotPEG.External.LarsenYuCoinTransport
import PegSeparation.CFLNotPEG.External.LarsenYuPairOverflow


open scoped BigOperators

namespace PegSeparation.External.LarsenYuCappedAdvantage

noncomputable section

open LarsenYuBernoulli LarsenYuBernoulliEvents LarsenYuCappedCodec
  LarsenYuCappedRecovery LarsenYuCoinTransport LarsenYuExperimentAdvantage
  LarsenYuMessageCodecBounds LarsenYuPairOverflow
  LarsenYuPayloadCardinality
  LarsenYuCappedCodec.CellProbe.StaticStructure
  LarsenYuCappedRecovery.CellProbe.StaticStructure
  LarsenYuExperimentAdvantage.CellProbe.StaticStructure
  LarsenYuPairOverflow.CellProbe.StaticStructure

namespace CellProbe.StaticStructure

variable {Input Query : Type} [Fintype Input] [Fintype Query]
  {wordBits cacheCells maxUpdatedCells : Nat}

local instance pairOverflowDecidable
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (p : ℝ) (input : Input) :
    DecidablePred (fun coin ↦ pairOverflow dataStructure p coin input) :=
  fun _ ↦ Classical.propDecidable _

theorem averagedPairOverflowMass_le_quarter_rpow
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (hlarge : 4 ≤ p * (maxUpdatedCells : ℝ)) :
    (∑ coin,
        (pairMaskDistribution (wordBits := wordBits) p hp hpone).mass coin *
          ∑ input, inputDistribution.mass input *
            if pairOverflow dataStructure p coin input then 1 else 0) ≤
      Real.rpow 2 (-(1 / 4 : ℝ) * p * maxUpdatedCells) := by
  classical
  let coinDistribution :=
    pairMaskDistribution (wordBits := wordBits) p hp hpone
  let error := Real.rpow 2 (-(1 / 4 : ℝ) * p * maxUpdatedCells)
  calc
    (∑ coin, coinDistribution.mass coin *
        ∑ input, inputDistribution.mass input *
          if pairOverflow dataStructure p coin input then 1 else 0) =
      ∑ input, inputDistribution.mass input *
        eventMass coinDistribution
          (fun coin ↦ pairOverflow dataStructure p coin input) := by
        unfold eventMass
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro input _hinput
        apply Finset.sum_congr rfl
        intro coin _hcoin
        ring
    _ ≤ ∑ input, inputDistribution.mass input * error := by
      apply Finset.sum_le_sum
      intro input _hinput
      exact mul_le_mul_of_nonneg_left
        (eventMass_pairOverflow_le_quarter_rpow dataStructure p hp hpone
          hlarge input)
        (inputDistribution.mass_nonnegative input)
    _ = error := by
      rw [← Finset.sum_mul, inputDistribution.mass_sum, one_mul]

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuCappedAdvantage
