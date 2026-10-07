import PegSeparation.CFLNotPEG.External.LarsenYuMessageCodecBounds


namespace PegSeparation.External.LarsenYuStrictMessageBound

noncomputable section

open LarsenYuMessageCodecBounds

theorem fixedMessageBits_lt
    {p : ℝ} {maxUpdatedCells cacheCells wordBits : Nat}
    (hword : 0 < wordBits)
    (hlarge : 4 ≤ p * (maxUpdatedCells : ℝ)) :
    (fixedMessageBits p maxUpdatedCells cacheCells wordBits : ℝ) <
      (8 * p * (maxUpdatedCells : ℝ) + (cacheCells : ℝ)) *
          (wordBits : ℝ) + 2 := by
  have hcap := sampleCap_cast_lt hlarge
  have hwordReal : 0 < (wordBits : ℝ) := by exact_mod_cast hword
  norm_num [fixedMessageBits]
  nlinarith

end

end PegSeparation.External.LarsenYuStrictMessageBound
