import PegSeparation.CFLNotPEG.External.LarsenYuCappedCodec
import PegSeparation.CFLNotPEG.External.LarsenYuOverflowRpow

open scoped BigOperators

namespace PegSeparation.External.LarsenYuPairOverflow

noncomputable section

open LarsenYuBernoulli LarsenYuBernoulliEvents LarsenYuCappedCodec
  LarsenYuFiniteMarkov LarsenYuJointCosts LarsenYuOverflow
  LarsenYuOverflowRpow
  LarsenYuCappedCodec.CellProbe.StaticStructure

theorem eventMass_product_fst
    {First Second : Type} [Fintype First] [Fintype Second]
    (first : FiniteDistribution First) (second : FiniteDistribution Second)
    (event : First → Prop) [DecidablePred event] :
    eventMass (productDistribution First Second first second)
        (fun pair ↦ event pair.1) =
      eventMass first event := by
  classical
  unfold eventMass productDistribution
  rw [Fintype.sum_prod_type]
  calc
    (∑ firstOutcome : First, ∑ secondOutcome : Second,
        first.mass firstOutcome * second.mass secondOutcome *
          (if event firstOutcome then 1 else 0)) =
        ∑ firstOutcome : First,
          (first.mass firstOutcome * (if event firstOutcome then 1 else 0)) *
            ∑ secondOutcome : Second, second.mass secondOutcome := by
      apply Finset.sum_congr rfl
      intro firstOutcome _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro secondOutcome _
      ring
    _ = ∑ firstOutcome : First,
        first.mass firstOutcome * (if event firstOutcome then 1 else 0) := by
      simp [second.mass_sum]


theorem eventMass_product_snd
    {First Second : Type} [Fintype First] [Fintype Second]
    (first : FiniteDistribution First) (second : FiniteDistribution Second)
    (event : Second → Prop) [DecidablePred event] :
    eventMass (productDistribution First Second first second)
        (fun pair ↦ event pair.2) =
      eventMass second event := by
  classical
  unfold eventMass productDistribution
  rw [Fintype.sum_prod_type]
  calc
    (∑ firstOutcome : First, ∑ secondOutcome : Second,
        first.mass firstOutcome * second.mass secondOutcome *
          (if event secondOutcome then 1 else 0)) =
        ∑ firstOutcome : First, first.mass firstOutcome *
          (∑ secondOutcome : Second,
            second.mass secondOutcome *
              (if event secondOutcome then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro firstOutcome _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro secondOutcome _
      ring
    _ = ∑ secondOutcome : Second,
        second.mass secondOutcome * (if event secondOutcome then 1 else 0) := by
      rw [← Finset.sum_mul, first.mass_sum, one_mul]

theorem eventMass_congr_events
    {Outcome : Type} [Fintype Outcome]
    (distribution : FiniteDistribution Outcome)
    (left right : Outcome → Prop)
    [DecidablePred left] [DecidablePred right]
    (hiff : ∀ outcome, left outcome ↔ right outcome) :
    eventMass distribution left = eventMass distribution right := by
  classical
  unfold eventMass
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases hleft : left outcome
  · have hright := (hiff outcome).mp hleft
    simp [hleft, hright]
  · have hright : ¬ right outcome := fun hright ↦ hleft ((hiff outcome).mpr hright)
    simp [hleft, hright]

namespace CellProbe.StaticStructure
variable {Input Query : Type} [Fintype Input] [Fintype Query]
  {wordBits cacheCells maxUpdatedCells : Nat}

def pairMaskDistribution (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1) :
    FiniteDistribution
      (Mask (CellProbe.Address wordBits) × Mask (CellProbe.Address wordBits)) :=
  productDistribution _ _
    (maskDistribution (CellProbe.Address wordBits) p hp hpone)
    (maskDistribution (CellProbe.Address wordBits) p hp hpone)

local instance pairOverflowDecidable
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells) (p : ℝ) (input : Input) :
    DecidablePred (fun coin ↦ pairOverflow dataStructure p coin input) :=
  fun _ ↦ Classical.propDecidable _

theorem eventMass_pairOverflow_le_quarter_rpow
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (hlarge : 4 ≤ p * (maxUpdatedCells : ℝ))
    (input : Input) :
    eventMass (pairMaskDistribution (wordBits := wordBits) p hp hpone)
        (fun coin ↦ pairOverflow dataStructure p coin input) ≤
      Real.rpow 2 (-(1 / 4 : ℝ) * p * maxUpdatedCells) := by
  classical
  let maskDist :=
    maskDistribution (CellProbe.Address wordBits) p hp hpone
  have hsingle :
      eventMass maskDist
          (fun selected ↦ sampleOverflow dataStructure p selected input) ≤
        Real.exp (-(2 * Real.log 2 - 1) * p * maxUpdatedCells) := by
    have hraw := eventMass_two_mul_cap_le_selectedCount_le
        p hp hpone maxUpdatedCells
        (dataStructure.updatedAddresses input)
        (dataStructure.updateBound input)
    calc
      eventMass maskDist
          (fun selected ↦ sampleOverflow dataStructure p selected input) =
        eventMass maskDist (fun selected ↦
          2 * p * (maxUpdatedCells : ℝ) ≤
            (LarsenYuBernoulliTail.selectedCount selected
              (dataStructure.updatedAddresses input) : ℝ)) := by
        apply eventMass_congr_events
        intro selected
        rfl
      _ ≤ Real.exp (-(2 * Real.log 2 - 1) * p * maxUpdatedCells) := by
        simpa [maskDist] using hraw
  have hfst :
      eventMass (pairMaskDistribution (wordBits := wordBits) p hp hpone)
          (fun coin ↦ sampleOverflow dataStructure p coin.1 input) =
        eventMass maskDist
          (fun selected ↦ sampleOverflow dataStructure p selected input) := by
    simpa only [pairMaskDistribution, maskDist] using
      (eventMass_product_fst maskDist maskDist
        (fun selected ↦ sampleOverflow dataStructure p selected input))
  have hsnd :
      eventMass (pairMaskDistribution (wordBits := wordBits) p hp hpone)
          (fun coin ↦ sampleOverflow dataStructure p coin.2 input) =
        eventMass maskDist
          (fun selected ↦ sampleOverflow dataStructure p selected input) := by
    simpa only [pairMaskDistribution, maskDist] using
      (eventMass_product_snd maskDist maskDist
        (fun selected ↦ sampleOverflow dataStructure p selected input))
  calc
    eventMass (pairMaskDistribution (wordBits := wordBits) p hp hpone)
        (fun coin ↦ pairOverflow dataStructure p coin input) =
      eventMass (pairMaskDistribution (wordBits := wordBits) p hp hpone)
        (fun coin ↦ sampleOverflow dataStructure p coin.1 input ∨
          sampleOverflow dataStructure p coin.2 input) := by
      apply eventMass_congr_events
      intro coin
      rfl
    _ ≤ eventMass (pairMaskDistribution (wordBits := wordBits) p hp hpone)
          (fun coin ↦ sampleOverflow dataStructure p coin.1 input) +
        eventMass (pairMaskDistribution (wordBits := wordBits) p hp hpone)
          (fun coin ↦ sampleOverflow dataStructure p coin.2 input) :=
      eventMass_or_le_add _ _ _
    _ = eventMass maskDist
          (fun selected ↦ sampleOverflow dataStructure p selected input) +
        eventMass maskDist
          (fun selected ↦ sampleOverflow dataStructure p selected input) := by
      rw [hfst, hsnd]
    _ ≤ Real.exp (-(2 * Real.log 2 - 1) * p * maxUpdatedCells) +
        Real.exp (-(2 * Real.log 2 - 1) * p * maxUpdatedCells) :=
      add_le_add hsingle hsingle
    _ = 2 * Real.exp (-(2 * Real.log 2 - 1) * p * maxUpdatedCells) := by ring

    _ ≤ Real.rpow 2 (-(1 / 4 : ℝ) * p * maxUpdatedCells) := by
      simpa only [mul_assoc] using
        (two_mul_exp_chernoff_le_quarter_rpow
          (p * (maxUpdatedCells : ℝ)) hlarge)

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuPairOverflow
