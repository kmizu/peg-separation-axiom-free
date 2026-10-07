import PegSeparation.CFLNotPEG.External.LarsenYuCappedCodec

open scoped BigOperators

namespace PegSeparation.External.LarsenYuCappedRecovery

noncomputable section

open LarsenYuBernoulli LarsenYuBaseView LarsenYuCappedCodec
  LarsenYuExperimentAdvantage LarsenYuFixedBlockCodec
  LarsenYuMessageCodecBounds LarsenYuNoopNormalization
  LarsenYuPayloadCardinality LarsenYuTruncation
  LarsenYuCappedCodec.CellProbe.StaticStructure
  LarsenYuExperimentAdvantage.CellProbe.StaticStructure

namespace CellProbe.StaticStructure

variable {Input Query : Type}
  {wordBits cacheCells maxUpdatedCells : Nat}

local instance pairOverflowDecidable
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (p : ℝ)
    (coin : Mask (CellProbe.Address wordBits) ×
      Mask (CellProbe.Address wordBits)) :
    DecidablePred (pairOverflow dataStructure p coin) :=
  fun _ ↦ Classical.propDecidable _

theorem recoverExperimentMessage_cappedEncode
    [Finite Input] [Finite Query]
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (heffective : ∀ input address,
      address ∈ dataStructure.updatedAddresses input →
        dataStructure.updatedWord input address ≠
          dataStructure.preMemory address)
    (p : ℝ)
    (coin : Mask (CellProbe.Address wordBits) ×
      Mask (CellProbe.Address wordBits))
    (input : Input)
    (hlarge : 4 ≤ p * (maxUpdatedCells : ℝ)) :
    recoverExperimentMessage dataStructure
        (cappedEncode dataStructure p coin input) =
      overflowCollapsed (experimentEncode dataStructure coin)
        (pairOverflow dataStructure p coin) input := by
  classical
  letI := Fintype.ofFinite Input
  letI := Fintype.ofFinite Query
  by_cases hfirst : sampleOverflow dataStructure p coin.1 input
  · simp [recoverExperimentMessage, cappedEncode, overflowCollapsed,
      pairOverflow, hfirst]
  · by_cases hsecond : sampleOverflow dataStructure p coin.2 input
    · simp [recoverExperimentMessage, cappedEncode, overflowCollapsed,
        pairOverflow, hfirst, hsecond]
    · have hfirstCount :
          (LarsenYuBernoulliTail.selectedCount coin.1
              (dataStructure.updatedAddresses input) : ℝ) <
            2 * p * (maxUpdatedCells : ℝ) := by
        exact lt_of_not_ge hfirst
      have hsecondCount :
          (LarsenYuBernoulliTail.selectedCount coin.2
              (dataStructure.updatedAddresses input) : ℝ) <
            2 * p * (maxUpdatedCells : ℝ) := by
        exact lt_of_not_ge hsecond
      have hfirstFit :
          (sampledEntries dataStructure coin.1 input).length ≤
            sampleCap p maxUpdatedCells := by
        rw [length_sampledEntries]
        exact count_le_sampleCap_of_cast_lt hlarge hfirstCount
      have hsecondFit :
          (sampledEntries dataStructure coin.2 input).length ≤
            sampleCap p maxUpdatedCells := by
        rw [length_sampledEntries]
        exact count_le_sampleCap_of_cast_lt hlarge hsecondCount
      have hfirstDecode :
          decodeBlock (sentinelEntry dataStructure)
              (sampledBlock dataStructure (sampleCap p maxUpdatedCells)
                coin.1 input) =
            sampledEntries dataStructure coin.1 input := by
        exact decodeBlock_encodeBlock_of_le
          (sampleCap p maxUpdatedCells) (sentinelEntry dataStructure)
          (sampledEntries dataStructure coin.1 input) hfirstFit
          (sampledEntries_ne_sentinel dataStructure heffective coin.1 input)
      have hsecondDecode :
          decodeBlock (sentinelEntry dataStructure)
              (sampledBlock dataStructure (sampleCap p maxUpdatedCells)
                coin.2 input) =
            sampledEntries dataStructure coin.2 input := by
        exact decodeBlock_encodeBlock_of_le
          (sampleCap p maxUpdatedCells) (sentinelEntry dataStructure)
          (sampledEntries dataStructure coin.2 input) hsecondFit
          (sampledEntries_ne_sentinel dataStructure heffective coin.2 input)
      simp [recoverExperimentMessage, cappedEncode, overflowCollapsed,
        pairOverflow, hfirst, hsecond, hfirstDecode, hsecondDecode,
        payloadOfEntries_sampledEntries, experimentEncode,
        LarsenYuBaseView.CellProbe.StaticStructure.baseView]

theorem experimentPartitionL1_sub_pairOverflowMass_le_cappedEncode
    [Fintype Input] [Finite Query]
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (heffective : ∀ input address,
      address ∈ dataStructure.updatedAddresses input →
        dataStructure.updatedWord input address ≠
          dataStructure.preMemory address)
    (p : ℝ)
    (coin : Mask (CellProbe.Address wordBits) ×
      Mask (CellProbe.Address wordBits))
    (hlarge : 4 ≤ p * (maxUpdatedCells : ℝ))
    (weight signal : Input → ℝ)
    (hweight : ∀ input, 0 ≤ weight input)
    (hsignal : ∀ input, |signal input| ≤ 1) :
    (∑ originalMessage : ExperimentMessage wordBits cacheCells,
      |∑ input, weight input *
        (if experimentEncode dataStructure coin input = originalMessage
          then signal input else 0)|) -
      (∑ input, weight input *
        if pairOverflow dataStructure p coin input then 1 else 0) ≤
      ∑ cappedMessage : FixedPayload wordBits cacheCells
          (sampleCap p maxUpdatedCells),
        |∑ input, weight input *
          (if cappedEncode dataStructure p coin input = cappedMessage
            then signal input else 0)| := by
  classical
  letI := Fintype.ofFinite Query
  exact partitionL1_sub_overflowMass_le_of_recover
    weight signal (experimentEncode dataStructure coin)
    (cappedEncode dataStructure p coin)
    (pairOverflow dataStructure p coin)
    (recoverExperimentMessage dataStructure)
    (fun input ↦ recoverExperimentMessage_cappedEncode
      dataStructure heffective p coin input hlarge)
    hweight hsignal

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuCappedRecovery
