import PegSeparation.CFLNotPEG.LowerBound.Chronogram
import PegSeparation.CFLNotPEG.LowerBound.Parameters
import PegSeparation.CFLNotPEG.Reduction.SCAToCellProbe


namespace PegSeparation.LowerBound.LargeScale

open Filter
open scoped Topology
open PegSeparation.LowerBound.Chronogram
open PegSeparation.LowerBound.Parameters
open PegSeparation.Reduction.SCAToCellProbe

def logScale (R : ℕ) : ℕ := R ^ 16

def updateCount (R : ℕ) : ℕ := 2 ^ logScale R

def queryCount (R : ℕ) : ℕ := updateCount R ^ 2

def epochBase (R : ℕ) : ℕ := 2 ^ R

def epochCount (R : ℕ) : ℕ := R ^ 15

def epochDimension (R i : ℕ) : ℕ := epochBase R ^ i

def scaUpdateBudget (degree radius : ℕ) : ℕ :=
  perSymbolBudget degree radius

def scaWordFactor
    (stateCount workLabelCount degree radius : ℕ) : ℕ :=
  5 + stateCount + workLabelCount + degree + radius +
    scaUpdateBudget degree radius

def wordBits (stateCount workLabelCount degree radius R : ℕ) : ℕ :=
  scaWordFactor stateCount workLabelCount degree radius * logScale R

noncomputable def sampleProbability (R : ℕ) : ℝ :=
  samplingProbability (logScale R : ℝ) 4

noncomputable def logInvSample (R : ℕ) : ℝ :=
  PegSeparation.log₂ (1 / sampleProbability R)

noncomputable def totalProbeBudget (degree radius R : ℕ) : ℝ :=
  (5 * scaUpdateBudget degree radius : ℕ) * (logScale R : ℝ)

noncomputable def updatedProbeBudget (degree radius R : ℕ) : ℝ :=
  (40 * scaUpdateBudget degree radius : ℕ) * (R : ℝ)

noncomputable def lambdaBudget (degree radius R : ℕ) : ℝ :=
  1 + updatedProbeBudget degree radius R * logInvSample R

def updatedCells (degree radius R i : ℕ) : ℕ :=
  scaUpdateBudget degree radius * epochDimension R i

def cacheCells (degree radius R i : ℕ) : ℕ :=
  4 * scaUpdateBudget degree radius * epochBase R ^ (i - 1)

lemma scaUpdateBudget_pos (degree radius : ℕ) :
    0 < scaUpdateBudget degree radius := by
  unfold scaUpdateBudget perSymbolBudget
  omega

lemma scaWordFactor_ge_five
    (stateCount workLabelCount degree radius : ℕ) :
    5 ≤ scaWordFactor stateCount workLabelCount degree radius := by
  unfold scaWordFactor
  omega

lemma epochBase_pow_epochCount (R : ℕ) :
    epochBase R ^ epochCount R = updateCount R := by
  simp only [epochBase, epochCount, updateCount, logScale]
  rw [← pow_mul]
  congr 1
  ring

lemma updateCount_cast (R : ℕ) :
    (updateCount R : ℝ) = (2 : ℝ) ^ (logScale R : ℝ) := by
  rw [updateCount, Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]

lemma epochBase_ge_two {R : ℕ} (hR : 1 ≤ R) : 2 ≤ epochBase R := by
  unfold epochBase
  have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hR
  simpa using h

lemma epochCount_ge_two {R : ℕ} (hR : 2 ≤ R) : 2 ≤ epochCount R := by
  unfold epochCount
  have hone : 1 < R ^ 15 := one_lt_pow₀ (by omega) (by norm_num)
  omega

lemma geometric_epochs_fit {R : ℕ} (hR : 1 ≤ R) :
    peeledMass (epochBase R) (epochCount R) < updateCount R := by
  apply peeledMass_lt_updates (epochBase_ge_two hR)
  exact (epochBase_pow_epochCount R).le

lemma clog_updateCount_succ_le (R : ℕ) :
    Nat.clog 2 (updateCount R + 1) ≤ logScale R + 1 := by
  apply Nat.clog_le_of_le_pow
  rw [updateCount, pow_succ]
  have hone : 1 ≤ 2 ^ logScale R := Nat.one_le_two_pow
  omega

lemma hardQuery_probe_budget {R : ℕ} (hR : 1 ≤ R) (degree radius : ℕ) :
    hardQueryLength (updateCount R) * scaUpdateBudget degree radius ≤
      5 * scaUpdateBudget degree radius * logScale R := by
  have hquery := hardQueryLength_le (updateCount R)
  have hclog := clog_updateCount_succ_le R
  have hL : 1 ≤ logScale R := by
    unfold logScale
    have : 0 < R ^ 16 := pow_pos (by omega) _
    omega
  have hlength : hardQueryLength (updateCount R) ≤ 5 * logScale R := by
    calc
      hardQueryLength (updateCount R) ≤
          1 + 2 * Nat.clog 2 (updateCount R + 1) := hquery
      _ ≤ 1 + 2 * (logScale R + 1) := by omega
      _ ≤ 5 * logScale R := by omega
  calc
    hardQueryLength (updateCount R) * scaUpdateBudget degree radius ≤
        (5 * logScale R) * scaUpdateBudget degree radius :=
      Nat.mul_le_mul_right _ hlength
    _ = 5 * scaUpdateBudget degree radius * logScale R := by ring

lemma hardQuery_fits_word {R : ℕ} (hR : 1 ≤ R)
    (stateCount workLabelCount degree radius : ℕ) :
    hardQueryLength (updateCount R) ≤
      wordBits stateCount workLabelCount degree radius R := by
  have hlength : hardQueryLength (updateCount R) ≤ 5 * logScale R := by
    have hquery := hardQueryLength_le (updateCount R)
    have hclog := clog_updateCount_succ_le R
    have hL : 1 ≤ logScale R := by
      unfold logScale
      have : 0 < R ^ 16 := pow_pos (by omega) _
      omega
    calc
      hardQueryLength (updateCount R) ≤
          1 + 2 * Nat.clog 2 (updateCount R + 1) := hquery
      _ ≤ 1 + 2 * (logScale R + 1) := by omega
      _ ≤ 5 * logScale R := by omega
  unfold wordBits
  exact hlength.trans (Nat.mul_le_mul_right (logScale R)
    (scaWordFactor_ge_five stateCount workLabelCount degree radius))

lemma eventually_const_mul_pow_le_two_pow (C : ℝ) (k : ℕ) :
    ∀ᶠ R : ℕ in atTop, C * (R : ℝ) ^ k ≤ (2 : ℝ) ^ R := by
  have h :=
    (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) k
      (by norm_num : (1 : ℝ) < 2)).const_mul_left C
  filter_upwards [h.eventuallyLE, eventually_ge_atTop 0] with R hR _
  have hnorm : |C| * (R : ℝ) ^ k ≤ (2 : ℝ) ^ R := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ R by positivity),
      abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) R)] using hR
  exact (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans hnorm

lemma middleEpochs_card_of_six_dvd {R : ℕ} (hR : 1 ≤ R) (hdiv : 6 ∣ R) :
    (middleEpochs (epochCount R)).card = epochCount R / 2 + 1 := by
  obtain ⟨q, rfl⟩ := hdiv
  have hell : (6 * q) ^ 15 = 6 * (6 ^ 14 * q ^ 15) := by ring
  simp only [epochCount, card_middleEpochs, hell]
  omega

lemma logScale_cast_eq_root_pow (R : ℕ) :
    (logScale R : ℝ) = (R : ℝ) ^ 16 := by
  simp [logScale]

lemma sixteenthRoot_logScale (R : ℕ) :
    sixteenthRoot (logScale R : ℝ) = (R : ℝ) := by
  rw [logScale_cast_eq_root_pow]
  simpa [sixteenthRoot, one_div] using
    (Real.pow_rpow_inv_natCast (show (0 : ℝ) ≤ R by positivity)
      (by norm_num : (16 : ℕ) ≠ 0))

lemma logInvSample_eq {R : ℕ} (hR : 1 ≤ R) :
    logInvSample R = (4 : ℝ) * Real.logb 2 (logScale R : ℝ) := by
  have hL : 0 < (logScale R : ℝ) := by
    exact_mod_cast (show 0 < logScale R by
      unfold logScale
      positivity)
  have hlog := logb_inv_samplingProbability hL 4
  unfold logInvSample PegSeparation.log₂
  simpa only [Real.logb, one_div, sampleProbability, Nat.cast_ofNat] using hlog

lemma logInvSample_le {R : ℕ} (hR : 1 ≤ R) :
    logInvSample R ≤ (64 / Real.log 2) * (R : ℝ) := by
  rw [logInvSample_eq hR]
  have hlog := logb_le_sixteenth_root
    (show 0 ≤ (logScale R : ℝ) by positivity)
  rw [sixteenthRoot_logScale] at hlog
  calc
    (4 : ℝ) * Real.logb 2 (logScale R : ℝ) ≤
        4 * ((16 / Real.log 2) * (R : ℝ)) := by gcongr
    _ = (64 / Real.log 2) * (R : ℝ) := by ring

lemma logInvSample_nonneg {R : ℕ} (hR : 1 ≤ R) : 0 ≤ logInvSample R := by
  rw [logInvSample_eq hR]
  have hL : (1 : ℝ) ≤ (logScale R : ℝ) := by
    exact_mod_cast (show 1 ≤ logScale R by
      unfold logScale
      exact Nat.one_le_pow 16 R (by omega))
  exact mul_nonneg (by norm_num)
    (Real.logb_nonneg (by norm_num) hL)

lemma sampleProbability_pos {R : ℕ} (hR : 1 ≤ R) :
    0 < sampleProbability R := by
  apply samplingProbability_pos
  exact_mod_cast (show 0 < logScale R by
    unfold logScale
    positivity)

lemma sampleProbability_le_half {R : ℕ} (hR : 2 ≤ R) :
    sampleProbability R ≤ (1 / 2 : ℝ) := by
  have hL : (2 : ℝ) ≤ (logScale R : ℝ) := by
    have hpow : R ≤ R ^ 16 := by
      exact Nat.le_pow (by omega)
    exact_mod_cast hR.trans hpow
  have hpow : (2 : ℝ) ≤ (logScale R : ℝ) ^ 4 := by
    calc
      (2 : ℝ) ≤ 2 ^ 4 := by norm_num
      _ ≤ (logScale R : ℝ) ^ 4 := by gcongr
  unfold sampleProbability samplingProbability
  rw [one_div]
  exact (inv_le_inv₀ (pow_pos (lt_of_lt_of_le (by norm_num) hL) 4)
    (by norm_num : (0 : ℝ) < 2)).2 hpow

lemma middle_dimension_pow_six_le {R i : ℕ}
    (hi : i ∈ middleEpochs (epochCount R)) :
    epochDimension R i ^ 6 ≤ updateCount R ^ 5 := by
  have hiUpper : 6 * i ≤ 5 * epochCount R := by
    rw [mem_middleEpochs] at hi
    omega
  have hbase : 0 < epochBase R := by
    unfold epochBase
    exact Nat.pow_pos (by norm_num)
  have hpow : epochBase R ^ (6 * i) ≤ epochBase R ^ (5 * epochCount R) :=
    Nat.pow_le_pow_right hbase hiUpper
  calc
    epochDimension R i ^ 6 = epochBase R ^ (6 * i) := by
      unfold epochDimension
      rw [← pow_mul, Nat.mul_comm i 6]
    _ ≤ epochBase R ^ (5 * epochCount R) := hpow
    _ = updateCount R ^ 5 := by
      rw [Nat.mul_comm 5 (epochCount R), pow_mul,
        epochBase_pow_epochCount]

lemma cast_le_five_six_rpow {d n : ℕ} (hd : 0 < d)
    (hpow : d ^ 6 ≤ n ^ 5) :
    (d : ℝ) ≤ (n : ℝ) ^ (5 / 6 : ℝ) := by
  have hcast : (d : ℝ) ^ 6 ≤ (n : ℝ) ^ 5 := by exact_mod_cast hpow
  calc
    (d : ℝ) = ((d : ℝ) ^ 6) ^ (1 / 6 : ℝ) := by
      symm
      simpa [one_div] using
        (Real.pow_rpow_inv_natCast (show (0 : ℝ) ≤ d by positivity)
          (by norm_num : (6 : ℕ) ≠ 0))
    _ ≤ ((n : ℝ) ^ 5) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hcast (by norm_num)
    _ = (n : ℝ) ^ (5 / 6 : ℝ) := by
      rw [← Real.rpow_natCast_mul (show (0 : ℝ) ≤ n by positivity)]
      congr 1
      norm_num

lemma middle_dimension_upper {R i : ℕ}
    (hi : i ∈ middleEpochs (epochCount R)) :
    (epochDimension R i : ℝ) ≤
      (updateCount R : ℝ) ^ (5 / 6 : ℝ) := by
  apply cast_le_five_six_rpow (by
    unfold epochDimension epochBase
    exact Nat.pow_pos (Nat.pow_pos (by norm_num)))
  exact middle_dimension_pow_six_le hi

lemma middle_index_pos {R i : ℕ} (hR : 2 ≤ R)
    (hi : i ∈ middleEpochs (epochCount R)) : 1 ≤ i := by
  rw [mem_middleEpochs] at hi
  have hell : 2 ≤ epochCount R := epochCount_ge_two hR
  omega

lemma epochBase_le_middle_dimension {R i : ℕ} (hR : 2 ≤ R)
    (hi : i ∈ middleEpochs (epochCount R)) :
    epochBase R ≤ epochDimension R i := by
  unfold epochDimension
  have hbase : 0 < epochBase R := by
    unfold epochBase
    exact Nat.pow_pos (by norm_num)
  simpa only [pow_one] using
    Nat.pow_le_pow_right hbase (middle_index_pos hR hi)

lemma context_fixed_updated_budget {R : ℕ} (hR : 1 ≤ R) (hdiv : 6 ∣ R)
    (degree radius : ℕ) :
    4 * totalProbeBudget degree radius R ≤
      updatedProbeBudget degree radius R *
        ((middleEpochs (epochCount R)).card : ℝ) := by
  have hcard := middleEpochs_card_of_six_dvd hR hdiv
  have hellEven : epochCount R / 2 * 2 = epochCount R := by
    obtain ⟨q, hq⟩ := hdiv
    have htwo : 2 ∣ epochCount R := by
      refine ⟨2 ^ 14 * (3 * q) ^ 15, ?_⟩
      simp only [epochCount, hq]
      ring
    exact Nat.div_mul_cancel htwo
  have hcastCard : ((epochCount R : ℝ) / 2) ≤
      ((middleEpochs (epochCount R)).card : ℝ) := by
    have hhalfCast :
        (epochCount R : ℝ) / 2 = ((epochCount R / 2 : ℕ) : ℝ) := by
      calc
        (epochCount R : ℝ) / 2 =
            (((epochCount R / 2) * 2 : ℕ) : ℝ) / 2 := by rw [hellEven]
        _ = ((epochCount R / 2 : ℕ) : ℝ) := by norm_num
    rw [hhalfCast]
    rw [hcard]
    exact_mod_cast Nat.le_succ (epochCount R / 2)
  have hscale : (logScale R : ℝ) = (R : ℝ) * (epochCount R : ℝ) := by
    simp only [logScale, epochCount, Nat.cast_pow]
    ring
  unfold totalProbeBudget updatedProbeBudget
  have htu : 0 ≤ (scaUpdateBudget degree radius : ℝ) := by positivity
  calc
    4 * ((5 * scaUpdateBudget degree radius : ℕ) * (logScale R : ℝ)) =
        (20 * (scaUpdateBudget degree radius : ℝ)) *
          ((R : ℝ) * (epochCount R : ℝ)) := by
      rw [hscale]
      norm_num
      ring
    _ = (40 * (scaUpdateBudget degree radius : ℝ) * (R : ℝ)) *
          ((epochCount R : ℝ) / 2) := by ring
    _ ≤ ((40 * scaUpdateBudget degree radius : ℕ) * (R : ℝ)) *
          ((middleEpochs (epochCount R)).card : ℝ) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      exact mul_le_mul_of_nonneg_left hcastCard (by positivity)

end PegSeparation.LowerBound.LargeScale
