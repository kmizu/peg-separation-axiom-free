import Mathlib


namespace PegSeparation.External.LarsenYuMessageCodecBounds

noncomputable section

def sampleCap (p : ℝ) (maxUpdatedCells : Nat) : Nat :=
  ⌈2 * p * (maxUpdatedCells : ℝ)⌉₊ - 1

def fixedMessageBits (p : ℝ) (maxUpdatedCells cacheCells wordBits : Nat) : Nat :=
  4 * sampleCap p maxUpdatedCells * wordBits + cacheCells * wordBits + 2

theorem sampleCap_cast_lt
    {p : ℝ} {maxUpdatedCells : Nat}
    (hlarge : 4 ≤ p * (maxUpdatedCells : ℝ)) :
    (sampleCap p maxUpdatedCells : ℝ) <
      2 * p * (maxUpdatedCells : ℝ) := by
  let threshold : ℝ := 2 * p * (maxUpdatedCells : ℝ)
  have hthreshold : 0 < threshold := by
    dsimp only [threshold]
    nlinarith
  have hceilPositive : 0 < ⌈threshold⌉₊ := Nat.ceil_pos.mpr hthreshold
  have hceil : (⌈threshold⌉₊ : ℝ) < threshold + 1 :=
    Nat.ceil_lt_add_one hthreshold.le
  have hcastSub : ((⌈threshold⌉₊ - 1 : Nat) : ℝ) =
      (⌈threshold⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub]
    · norm_num
    · exact hceilPositive
  change ((⌈threshold⌉₊ - 1 : Nat) : ℝ) < threshold
  rw [hcastSub]
  linarith

theorem count_le_sampleCap_of_cast_lt
    {p : ℝ} {maxUpdatedCells count : Nat}
    (hlarge : 4 ≤ p * (maxUpdatedCells : ℝ))
    (hcount : (count : ℝ) < 2 * p * (maxUpdatedCells : ℝ)) :
    count ≤ sampleCap p maxUpdatedCells := by
  let threshold : ℝ := 2 * p * (maxUpdatedCells : ℝ)
  have hthreshold : 0 < threshold := by
    dsimp only [threshold]
    nlinarith
  have hceilPositive : 0 < ⌈threshold⌉₊ := Nat.ceil_pos.mpr hthreshold
  have hceilUpper : threshold ≤ (⌈threshold⌉₊ : ℝ) :=
    Nat.le_ceil threshold
  have hcountCeilReal : (count : ℝ) < (⌈threshold⌉₊ : ℝ) := by
    have hcountThreshold : (count : ℝ) < threshold := by
      simpa [threshold] using hcount
    exact hcountThreshold.trans_le hceilUpper
  have hcountCeil : count < ⌈threshold⌉₊ := by
    exact_mod_cast hcountCeilReal
  have hcountCeil' : count < ⌈2 * p * (maxUpdatedCells : ℝ)⌉₊ := by
    simpa [threshold] using hcountCeil
  unfold sampleCap
  have hceilPositive' : 0 < ⌈2 * p * (maxUpdatedCells : ℝ)⌉₊ := by
    simpa [threshold] using hceilPositive
  omega

theorem cast_lt_threshold_of_count_le_sampleCap
    {p : ℝ} {maxUpdatedCells count : Nat}
    (hlarge : 4 ≤ p * (maxUpdatedCells : ℝ))
    (hcount : count ≤ sampleCap p maxUpdatedCells) :
    (count : ℝ) < 2 * p * (maxUpdatedCells : ℝ) := by
  have hcountCast :
      (count : ℝ) ≤ (sampleCap p maxUpdatedCells : ℝ) := by
    exact_mod_cast hcount
  exact hcountCast.trans_lt (sampleCap_cast_lt hlarge)

theorem fixedMessageBits_le
    {p : ℝ} {maxUpdatedCells cacheCells wordBits : Nat}
    (hword : 0 < wordBits)
    (hlarge : 4 ≤ p * (maxUpdatedCells : ℝ)) :
    (fixedMessageBits p maxUpdatedCells cacheCells wordBits : ℝ) ≤
      (8 * p * (maxUpdatedCells : ℝ) + (cacheCells : ℝ)) *
          (wordBits : ℝ) + 2 := by
  have hcap := sampleCap_cast_lt hlarge
  have hwordReal : 0 < (wordBits : ℝ) := by exact_mod_cast hword
  norm_num [fixedMessageBits]
  nlinarith

end

end PegSeparation.External.LarsenYuMessageCodecBounds
