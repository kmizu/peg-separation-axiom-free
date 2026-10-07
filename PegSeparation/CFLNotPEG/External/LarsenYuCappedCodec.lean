import PegSeparation.CFLNotPEG.External.LarsenYuExperimentAdvantage
import PegSeparation.CFLNotPEG.External.LarsenYuBernoulliTail
import PegSeparation.CFLNotPEG.External.LarsenYuFixedBlockCodec
import PegSeparation.CFLNotPEG.External.LarsenYuMessageCodecBounds
import PegSeparation.CFLNotPEG.External.LarsenYuNoopNormalization
import PegSeparation.CFLNotPEG.External.LarsenYuPayloadCardinality
import PegSeparation.CFLNotPEG.External.LarsenYuTruncation


namespace PegSeparation.External.LarsenYuCappedCodec

noncomputable section

open LarsenYuBernoulli LarsenYuBernoulliTail LarsenYuBaseView
  LarsenYuExperimentAdvantage LarsenYuFixedBlockCodec
  LarsenYuMessageCodecBounds LarsenYuNoopNormalization
  LarsenYuPayloadCardinality LarsenYuTruncation
  LarsenYuBaseView.CellProbe.StaticStructure
  LarsenYuExperimentAdvantage.CellProbe.StaticStructure

abbrev CellEntry (wordBits : Nat) :=
  CellProbe.Address wordBits × CellProbe.Word wordBits

namespace CellProbe.StaticStructure

variable {Input Query : Type} [Fintype Input] [Fintype Query]
  {wordBits cacheCells maxUpdatedCells : Nat}

def selectedUpdatedAddresses
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selected : Mask (CellProbe.Address wordBits)) (input : Input) :
    List (CellProbe.Address wordBits) :=
  (dataStructure.updatedAddresses input |>.filter fun address ↦
    selected address = true).toList

def sampledEntries
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selected : Mask (CellProbe.Address wordBits)) (input : Input) :
    List (CellEntry wordBits) :=
  (selectedUpdatedAddresses dataStructure selected input).map fun address ↦
    (address, dataStructure.updatedWord input address)

def payloadOfEntries (entries : List (CellEntry wordBits)) :
    CellProbe.Address wordBits → Option (CellProbe.Word wordBits) :=
  fun address ↦ entries.lookup address

theorem lookup_graph_eq_none_of_not_mem
    {Address Word : Type} [BEq Address] [LawfulBEq Address]
    (word : Address → Word) (addresses : List Address) (address : Address)
    (hnot : address ∉ addresses) :
    (addresses.map fun a ↦ (a, word a)).lookup address = none := by
  induction addresses with
  | nil => simp
  | cons head tail ih =>
      simp only [List.mem_cons, not_or] at hnot
      have hbeq : (address == head) = false :=
        Bool.eq_false_of_not_eq_true fun htrue ↦
          hnot.1 (LawfulBEq.eq_of_beq htrue)
      simp [List.lookup, hbeq, ih hnot.2]

@[simp]
theorem length_sampledEntries
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selected : Mask (CellProbe.Address wordBits)) (input : Input) :
    (sampledEntries dataStructure selected input).length =
      selectedCount selected (dataStructure.updatedAddresses input) := by
  simp [sampledEntries, selectedUpdatedAddresses, selectedCount]

theorem payloadOfEntries_sampledEntries
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selected : Mask (CellProbe.Address wordBits)) (input : Input) :
    payloadOfEntries (sampledEntries dataStructure selected input) =
      (baseView dataStructure selected input).1 := by
  funext address
  by_cases hmem : address ∈ dataStructure.updatedAddresses input
  · by_cases hselected : selected address = true
    · have hin : address ∈
          selectedUpdatedAddresses dataStructure selected input := by
        simp [selectedUpdatedAddresses, hmem, hselected]
      unfold payloadOfEntries sampledEntries
      rw [List.lookup_graph (dataStructure.updatedWord input) hin]
      simp [baseView, hmem, hselected]
    · have hnot : address ∉
          selectedUpdatedAddresses dataStructure selected input := by
        simp [selectedUpdatedAddresses, hmem, hselected]
      unfold payloadOfEntries sampledEntries
      rw [lookup_graph_eq_none_of_not_mem (dataStructure.updatedWord input) _ _ hnot]
      simp [baseView, hmem, hselected]
  · have hnot : address ∉
        selectedUpdatedAddresses dataStructure selected input := by
      simp [selectedUpdatedAddresses, hmem]
    unfold payloadOfEntries sampledEntries
    rw [lookup_graph_eq_none_of_not_mem (dataStructure.updatedWord input) _ _ hnot]
    simp [baseView, hmem]

def sentinelEntry
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells) : CellEntry wordBits :=
  (0, dataStructure.preMemory 0)

theorem sampledEntries_ne_sentinel
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (heffective : ∀ input address,
      address ∈ dataStructure.updatedAddresses input →
        dataStructure.updatedWord input address ≠ dataStructure.preMemory address)
    (selected : Mask (CellProbe.Address wordBits)) (input : Input) :
    ∀ entry ∈ sampledEntries dataStructure selected input,
      entry ≠ sentinelEntry dataStructure := by
  intro entry hentry
  rcases List.mem_map.mp hentry with ⟨address, haddress, rfl⟩
  have hupdated : address ∈ dataStructure.updatedAddresses input := by
    have hfiltered : address ∈
        (dataStructure.updatedAddresses input).filter
          (fun candidate ↦ selected candidate = true) := by
      simpa [selectedUpdatedAddresses] using haddress
    exact (Finset.mem_filter.mp hfiltered).1
  intro heq
  have haddressZero : address = 0 := congrArg Prod.fst heq
  have hword := congrArg Prod.snd heq
  subst address
  exact heffective input 0 hupdated hword

def sampledBlock
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (blockCells : Nat)
    (selected : Mask (CellProbe.Address wordBits)) (input : Input) :
    FixedCellBlock wordBits blockCells :=
  encodeBlock blockCells (sentinelEntry dataStructure)
    (sampledEntries dataStructure selected input)

def sampleOverflow
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (p : ℝ) (selected : Mask (CellProbe.Address wordBits))
    (input : Input) : Prop :=
  2 * p * (maxUpdatedCells : ℝ) ≤
    (selectedCount selected (dataStructure.updatedAddresses input) : ℝ)


def pairOverflow
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (p : ℝ)
    (coin : Mask (CellProbe.Address wordBits) × Mask (CellProbe.Address wordBits))
    (input : Input) : Prop :=
  sampleOverflow dataStructure p coin.1 input ∨
    sampleOverflow dataStructure p coin.2 input


def cappedEncode
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (p : ℝ)
    (coin : Mask (CellProbe.Address wordBits) × Mask (CellProbe.Address wordBits))
    (input : Input) :
    FixedPayload wordBits cacheCells (sampleCap p maxUpdatedCells) := by
  classical
  let blockCells := sampleCap p maxUpdatedCells
  exact (sampledBlock dataStructure blockCells coin.1 input,
    sampledBlock dataStructure blockCells coin.2 input,
    dataStructure.cache input,
    decide (sampleOverflow dataStructure p coin.1 input),
    decide (sampleOverflow dataStructure p coin.2 input))

def recoverExperimentMessage {blockCells : Nat}
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (payload : FixedPayload wordBits cacheCells blockCells) :
    Option (ExperimentMessage wordBits cacheCells) :=
  match payload with
  | (firstBlock, secondBlock, cache, firstOverflow, secondOverflow) =>
      if firstOverflow || secondOverflow then none else
        some
          ((payloadOfEntries (decodeBlock (sentinelEntry dataStructure) firstBlock), cache),
            payloadOfEntries (decodeBlock (sentinelEntry dataStructure) secondBlock))

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuCappedCodec
