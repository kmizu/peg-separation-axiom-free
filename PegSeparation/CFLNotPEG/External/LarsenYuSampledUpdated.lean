import PegSeparation.CFLNotPEG.External.LarsenYuBernoulliEvents


namespace PegSeparation.External.LarsenYuSampledUpdated

noncomputable section

open LarsenYuBernoulli LarsenYuBernoulliEvents
local instance includesDecidable {Coordinate : Type} [Fintype Coordinate]
    [DecidableEq Coordinate] (mask : Mask Coordinate)
    (required : Finset Coordinate) : Decidable (Includes mask required) := by
  unfold Includes
  infer_instance


namespace CellProbe.StaticStructure

variable {Input Query : Type} {wordBits cacheCells maxUpdatedCells : Nat}

def probedUpdatedAddresses
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query) : Finset (CellProbe.Address wordBits) :=
  ((dataStructure.probeTrace input query).filter fun address ↦
    address ∈ dataStructure.updatedAddresses input).toFinset

theorem probedUpdatedAddresses_card_le_updatedProbeCount
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query) :
    (probedUpdatedAddresses dataStructure input query).card ≤
      dataStructure.updatedProbeCount input query := by
  unfold probedUpdatedAddresses CellProbe.StaticStructure.updatedProbeCount
  simpa [List.countP_eq_length_filter] using
    List.toFinset_card_le
      ((dataStructure.probeTrace input query).filter fun address ↦
        address ∈ dataStructure.updatedAddresses input)

theorem eventMass_includes_probedUpdatedAddresses
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1) :
    eventMass
        (maskDistribution (CellProbe.Address wordBits) p hp hpone)
        (fun mask ↦ Includes mask
          (probedUpdatedAddresses dataStructure input query)) =
      p ^ (probedUpdatedAddresses dataStructure input query).card :=
  eventMass_includes_maskDistribution p hp hpone _

theorem pow_updatedProbeCount_le_eventMass_includes
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1) :
    p ^ dataStructure.updatedProbeCount input query ≤
      eventMass
        (maskDistribution (CellProbe.Address wordBits) p hp hpone)
        (fun mask ↦ Includes mask
          (probedUpdatedAddresses dataStructure input query)) := by
  rw [eventMass_includes_probedUpdatedAddresses]
  exact pow_le_pow_of_le_one hp hpone
    (probedUpdatedAddresses_card_le_updatedProbeCount dataStructure input query)

theorem pow_bound_le_eventMass_includes
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (bound : Nat)
    (hcount : dataStructure.updatedProbeCount input query ≤ bound) :
    p ^ bound ≤
      eventMass
        (maskDistribution (CellProbe.Address wordBits) p hp hpone)
        (fun mask ↦ Includes mask
          (probedUpdatedAddresses dataStructure input query)) := by
  exact (pow_le_pow_of_le_one hp hpone hcount).trans
    (pow_updatedProbeCount_le_eventMass_includes dataStructure input query
      p hp hpone)

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuSampledUpdated
