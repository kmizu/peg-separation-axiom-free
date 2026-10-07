import PegSeparation.CFLNotPEG.LowerBound.LargeScale
import PegSeparation.CFLNotPEG.Reduction.MultiphaseModel


namespace PegSeparation.LowerBound.FamilyScale

open Filter
open scoped Topology
open PegSeparation.LowerBound.Chronogram
open PegSeparation.LowerBound.Parameters
open PegSeparation.LowerBound.LargeScale
open PegSeparation.Reduction

def familyWordBits (wordScale R : ℕ) : ℕ :=
  MultiphaseModel.scaledLogBudget wordScale (updateCount R)

def familyQueryReads (queryScale R : ℕ) : ℕ :=
  MultiphaseModel.scaledLogBudget queryScale (updateCount R)

def wordConstant (wordScale : ℕ) : ℕ := 3 * wordScale
def queryConstant (queryScale : ℕ) : ℕ := 3 * queryScale

def updatedConstant (queryScale : ℕ) : ℕ := 6 * queryScale

noncomputable def logConstant : ℝ := 64 / Real.log 2

noncomputable def lambdaConstant (queryScale : ℕ) : ℝ :=
  1 + (updatedConstant queryScale : ℝ) * logConstant

noncomputable def rootConstant (queryScale : ℕ) : ℝ :=
  1 + (queryConstant queryScale : ℝ) + lambdaConstant queryScale

noncomputable def familyLambda (queryScale R : ℕ) : ℝ :=
  1 + ((updatedConstant queryScale : ℕ) : ℝ) * (R : ℝ) *
    logInvSample R

noncomputable def familyExponent (A : ℝ) (queryScale R : ℕ) : ℝ :=
  correctedExponent A (familyQueryReads queryScale R : ℝ)
    (familyLambda queryScale R) (logInvSample R)

noncomputable def familyMessageCost
    (wordScale updateWrites R i : ℕ) : ℝ :=
  (8 * sampleProbability R *
        ((updateWrites * epochDimension R i : ℕ) : ℝ) +
      2 * ((updateWrites * peeledMass (epochBase R) i : ℕ) : ℝ)) *
      (familyWordBits wordScale R : ℝ) + 2

noncomputable def collisionRatio (R i : ℕ) : ℝ :=
  (updateCount R : ℝ) ^ 2 /
    ((2 ^ epochDimension R i : ℕ) : ℝ)

structure ScaleCertificate
    (wordScale queryScale updateWrites : ℕ) (A a : ℝ) (R : ℕ) : Prop where
  six_dvd : 6 ∣ R
  root_ge_six : 6 ≤ R
  geometry_power :
    epochBase R ^ epochCount R = updateCount R
  geometry_fit :
    peeledMass (epochBase R) (epochCount R) < updateCount R
  middle_nonempty :
    (middleEpochs (epochCount R)).Nonempty
  word_bound :
    familyWordBits wordScale R ≤ wordConstant wordScale * logScale R
  query_bound :
    familyQueryReads queryScale R ≤ queryConstant queryScale * logScale R
  query_per_middle_epoch :
    (familyQueryReads queryScale R : ℝ) /
        ((middleEpochs (epochCount R)).card : ℝ) ≤
      (updatedConstant queryScale : ℝ) * (R : ℝ)
  sample_pos : 0 < sampleProbability R
  sample_le_half : sampleProbability R ≤ (1 / 2 : ℝ)
  log_inverse_bound :
    logInvSample R ≤ logConstant * (R : ℝ)
  lambda_nonnegative : 0 ≤ familyLambda queryScale R
  lambda_bound :
    familyLambda queryScale R ≤ lambdaConstant queryScale * (R : ℝ) ^ 2
  exponent_bound :
    familyExponent A queryScale R ≤ (logScale R : ℝ) / 8
  dimension_ge_two : ∀ i ∈ middleEpochs (epochCount R),
    2 ≤ epochDimension R i
  dimension_ge_log : ∀ i ∈ middleEpochs (epochCount R),
    logScale R ≤ epochDimension R i
  dimension_le_five_sixths : ∀ i ∈ middleEpochs (epochCount R),
    (epochDimension R i : ℝ) ≤
      (updateCount R : ℝ) ^ (5 / 6 : ℝ)
  collision_lt_eighth : ∀ i ∈ middleEpochs (epochCount R),
    collisionRatio R i < (1 / 8 : ℝ)
  message_cap : ∀ i ∈ middleEpochs (epochCount R),
    familyMessageCost wordScale updateWrites R i ≤
      (epochDimension R i : ℝ) / 2
  overflow_budget : ∀ i ∈ middleEpochs (epochCount R),
    1 + (logScale R : ℝ) / 8 ≤
      a * sampleProbability R *
        ((updateWrites * epochDimension R i : ℕ) : ℝ)
  separation_threshold :
    6 < (2 : ℝ) ^ ((logScale R : ℝ) / 8)

lemma logConstant_pos : 0 < logConstant := by
  unfold logConstant
  exact div_pos (by norm_num) (Real.log_pos (by norm_num))

lemma lambdaConstant_nonneg (queryScale : ℕ) :
    0 ≤ lambdaConstant queryScale := by
  unfold lambdaConstant
  exact add_nonneg (by norm_num)
    (mul_nonneg (by positivity) logConstant_pos.le)

lemma rootConstant_nonneg (queryScale : ℕ) :
    0 ≤ rootConstant queryScale := by
  unfold rootConstant
  exact add_nonneg (add_nonneg (by norm_num) (by positivity))
    (lambdaConstant_nonneg queryScale)

lemma query_mul_lambda_le_root_sq (queryScale : ℕ) :
    (queryConstant queryScale : ℝ) * lambdaConstant queryScale ≤
      rootConstant queryScale ^ 2 := by
  have hq : 0 ≤ (queryConstant queryScale : ℝ) := by positivity
  have hl := lambdaConstant_nonneg queryScale
  unfold rootConstant
  nlinarith [mul_nonneg hq hl,
    sq_nonneg (1 + (queryConstant queryScale : ℝ) +
      lambdaConstant queryScale)]

lemma family_logScale_le {R : ℕ} (hR : 1 ≤ R) :
    MultiphaseModel.logScale (updateCount R) ≤ 3 * logScale R := by
  have hclog := clog_updateCount_succ_le R
  have hL : 1 ≤ logScale R := by
    unfold logScale
    have : 0 < R ^ 16 := pow_pos (by omega) _
    omega
  unfold MultiphaseModel.logScale
  omega

lemma familyWordBits_le {R : ℕ} (hR : 1 ≤ R) (wordScale : ℕ) :
    familyWordBits wordScale R ≤ wordConstant wordScale * logScale R := by
  unfold familyWordBits MultiphaseModel.scaledLogBudget wordConstant
  calc
    wordScale * MultiphaseModel.logScale (updateCount R) ≤
        wordScale * (3 * logScale R) :=
      Nat.mul_le_mul_left wordScale (family_logScale_le hR)
    _ = 3 * wordScale * logScale R := by ring

lemma familyQueryReads_le {R : ℕ} (hR : 1 ≤ R) (queryScale : ℕ) :
    familyQueryReads queryScale R ≤
      queryConstant queryScale * logScale R := by
  unfold familyQueryReads MultiphaseModel.scaledLogBudget queryConstant
  calc
    queryScale * MultiphaseModel.logScale (updateCount R) ≤
        queryScale * (3 * logScale R) :=
      Nat.mul_le_mul_left queryScale (family_logScale_le hR)
    _ = 3 * queryScale * logScale R := by ring

lemma familyQueryReads_per_middle_le {R : ℕ}
    (hR : 1 ≤ R) (hdiv : 6 ∣ R) (queryScale : ℕ) :
    (familyQueryReads queryScale R : ℝ) /
        ((middleEpochs (epochCount R)).card : ℝ) ≤
      (updatedConstant queryScale : ℝ) * (R : ℝ) := by
  have hquery := familyQueryReads_le hR queryScale
  have hcard := middleEpochs_card_of_six_dvd hR hdiv
  have htwo : epochCount R / 2 * 2 = epochCount R := by
    obtain ⟨q, hq⟩ := hdiv
    have heven : 2 ∣ epochCount R := by
      refine ⟨2 ^ 14 * (3 * q) ^ 15, ?_⟩
      simp only [epochCount, hq]
      ring
    exact Nat.div_mul_cancel heven
  have hcardLower : ((epochCount R : ℝ) / 2) ≤
      ((middleEpochs (epochCount R)).card : ℝ) := by
    have hhalfCast :
        (epochCount R : ℝ) / 2 = ((epochCount R / 2 : ℕ) : ℝ) := by
      calc
        (epochCount R : ℝ) / 2 =
            (((epochCount R / 2) * 2 : ℕ) : ℝ) / 2 := by rw [htwo]
        _ = ((epochCount R / 2 : ℕ) : ℝ) := by norm_num
    rw [hhalfCast]
    rw [hcard]
    exact_mod_cast Nat.le_succ (epochCount R / 2)
  have hellpos : 0 < (epochCount R : ℝ) / 2 := by
    unfold epochCount
    positivity
  have hcardpos : 0 < ((middleEpochs (epochCount R)).card : ℝ) :=
    hellpos.trans_le hcardLower
  rw [div_le_iff₀ hcardpos]
  have hqueryReal : (familyQueryReads queryScale R : ℝ) ≤
      (queryConstant queryScale : ℝ) * (logScale R : ℝ) := by
    exact_mod_cast hquery
  calc
    (familyQueryReads queryScale R : ℝ) ≤
        (queryConstant queryScale : ℝ) * (logScale R : ℝ) := hqueryReal
    _ = ((updatedConstant queryScale : ℝ) * (R : ℝ)) *
        ((epochCount R : ℝ) / 2) := by
      simp only [queryConstant, updatedConstant, logScale, epochCount,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
      ring
    _ ≤ ((updatedConstant queryScale : ℝ) * (R : ℝ)) *
        ((middleEpochs (epochCount R)).card : ℝ) := by
      gcongr

lemma familyLambda_nonneg {R : ℕ} (hR : 1 ≤ R) (queryScale : ℕ) :
    0 ≤ familyLambda queryScale R := by
  unfold familyLambda
  have := logInvSample_nonneg hR
  positivity

lemma familyLambda_le {R : ℕ} (hR : 1 ≤ R) (queryScale : ℕ) :
    familyLambda queryScale R ≤
      lambdaConstant queryScale * (R : ℝ) ^ 2 := by
  have hr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hlog := logInvSample_le hR
  have hlog' : logInvSample R ≤ logConstant * (R : ℝ) := by
    simpa [logConstant] using hlog
  have hCu : 0 ≤ (updatedConstant queryScale : ℝ) := by positivity
  have hR0 : 0 ≤ (R : ℝ) := by positivity
  calc
    familyLambda queryScale R =
        1 + (updatedConstant queryScale : ℝ) * (R : ℝ) *
          logInvSample R := by rfl
    _ ≤ 1 + (updatedConstant queryScale : ℝ) * (R : ℝ) *
          (logConstant * (R : ℝ)) := by gcongr
    _ = 1 + ((updatedConstant queryScale : ℝ) * logConstant) *
          (R : ℝ) ^ 2 := by ring
    _ ≤ lambdaConstant queryScale * (R : ℝ) ^ 2 := by
      unfold lambdaConstant
      nlinarith [sq_nonneg (R : ℝ)]

lemma message_sum_le_half
    {p uw d recent w : ℝ}
    (hd : 0 ≤ d)
    (hsampled : 64 * p * uw * w ≤ 1)
    (hcached : 16 * uw * recent * w ≤ d)
    (hd8 : 8 ≤ d) :
    (8 * p * (uw * d) + 2 * uw * recent) * w + 2 ≤ d / 2 := by
  have hsampled' := mul_le_mul_of_nonneg_right hsampled hd
  have hs : 8 * p * (uw * d) * w ≤ d / 8 := by
    nlinarith
  have hc : 2 * uw * recent * w ≤ d / 8 := by
    nlinarith
  have htwo : 2 ≤ d / 4 := by linarith
  nlinarith

structure ScaleThresholds
    (wordScale queryScale updateWrites : ℕ) (A a : ℝ) (R : ℕ) : Prop where
  root_ge_six : 6 ≤ R
  exponent_polynomial :
    8 * A * logConstant *
        (rootConstant queryScale + lambdaConstant queryScale) ≤
      (R : ℝ) ^ 6
  sampled_message :
    64 * (updateWrites : ℝ) * (wordConstant wordScale : ℝ) ≤
      (logScale R : ℝ) ^ 3
  cache_message :
    32 * (updateWrites : ℝ) * (wordConstant wordScale : ℝ) *
        (logScale R : ℝ) ≤
      (epochBase R : ℝ)
  dimension_gap :
    3 * (logScale R : ℝ) ≤ (epochBase R : ℝ)
  overflow_growth :
    (logScale R : ℝ) ^ 5 ≤
      4 * a * (updateWrites : ℝ) * (epochBase R : ℝ)

lemma exponent_bound_of_thresholds
    {queryScale R : ℕ} {A : ℝ} (hA : 0 < A) (hR : 1 ≤ R)
    (hthreshold :
      8 * A * logConstant *
          (rootConstant queryScale + lambdaConstant queryScale) ≤
        (R : ℝ) ^ 6) :
    familyExponent A queryScale R ≤ (logScale R : ℝ) / 8 := by
  apply correctedExponent_le_log_eighth
      (show 0 ≤ A from hA.le)
      (show (1 : ℝ) ≤ R by exact_mod_cast hR)
      (familyLambda_nonneg hR queryScale)
      (logInvSample_nonneg hR)
      (show 0 ≤ (queryConstant queryScale : ℝ) by positivity)
      (lambdaConstant_nonneg queryScale)
      (rootConstant_nonneg queryScale)
      logConstant_pos.le
      (logScale_cast_eq_root_pow R)
  · exact_mod_cast (familyQueryReads_le hR queryScale)
  · exact familyLambda_le hR queryScale
  · exact logInvSample_le hR
  · exact query_mul_lambda_le_root_sq queryScale
  · exact hthreshold

lemma peeledMass_mul_epochBase_le_two_dimension
    {R i : ℕ} (hR : 1 ≤ R) (hi : 1 ≤ i) :
    peeledMass (epochBase R) i * epochBase R ≤
      2 * epochDimension R i := by
  have hraw := peeledMass_succ_le_two_mul_prev (epochBase_ge_two hR) (i - 1)
  have hisub : i - 1 + 1 = i := by omega
  rw [hisub] at hraw
  calc
    peeledMass (epochBase R) i * epochBase R ≤
        (2 * epochBase R ^ (i - 1)) * epochBase R :=
      Nat.mul_le_mul_right (epochBase R) hraw
    _ = 2 * epochDimension R i := by
      unfold epochDimension
      rw [Nat.mul_assoc, ← pow_succ, hisub]

lemma sample_message_coefficient_le_one
    {wordScale updateWrites R : ℕ} (hR : 1 ≤ R)
    (hthreshold :
      64 * (updateWrites : ℝ) * (wordConstant wordScale : ℝ) ≤
        (logScale R : ℝ) ^ 3) :
    64 * sampleProbability R * (updateWrites : ℝ) *
        (familyWordBits wordScale R : ℝ) ≤ 1 := by
  have hL : 0 < (logScale R : ℝ) := by
    exact_mod_cast (show 0 < logScale R by
      unfold logScale
      positivity)
  have hwNat := familyWordBits_le hR wordScale
  have hw : (familyWordBits wordScale R : ℝ) ≤
      (wordConstant wordScale : ℝ) * (logScale R : ℝ) := by
    exact_mod_cast hwNat
  have hden : 0 < (logScale R : ℝ) ^ 3 := pow_pos hL 3
  have hp : 0 ≤ sampleProbability R := (sampleProbability_pos hR).le
  calc
    64 * sampleProbability R * (updateWrites : ℝ) *
        (familyWordBits wordScale R : ℝ) ≤
      64 * sampleProbability R * (updateWrites : ℝ) *
        ((wordConstant wordScale : ℝ) * (logScale R : ℝ)) := by
          gcongr
    _ = (64 * (updateWrites : ℝ) * (wordConstant wordScale : ℝ)) /
        (logScale R : ℝ) ^ 3 := by
      unfold sampleProbability samplingProbability
      field_simp
    _ ≤ (logScale R : ℝ) ^ 3 / (logScale R : ℝ) ^ 3 := by
      exact div_le_div_of_nonneg_right hthreshold hden.le
    _ = 1 := div_self hden.ne'

lemma cached_message_coefficient_le_dimension
    {wordScale updateWrites R i : ℕ} (hR : 1 ≤ R) (hi : 1 ≤ i)
    (hthreshold :
      32 * (updateWrites : ℝ) * (wordConstant wordScale : ℝ) *
          (logScale R : ℝ) ≤
        (epochBase R : ℝ)) :
    16 * (updateWrites : ℝ) *
        (peeledMass (epochBase R) i : ℝ) *
        (familyWordBits wordScale R : ℝ) ≤
      (epochDimension R i : ℝ) := by
  have hwNat := familyWordBits_le hR wordScale
  have hw : (familyWordBits wordScale R : ℝ) ≤
      (wordConstant wordScale : ℝ) * (logScale R : ℝ) := by
    exact_mod_cast hwNat
  have hmassNat := peeledMass_mul_epochBase_le_two_dimension hR hi
  have hmass :
      (peeledMass (epochBase R) i : ℝ) * (epochBase R : ℝ) ≤
        2 * (epochDimension R i : ℝ) := by
    exact_mod_cast hmassNat
  calc
    16 * (updateWrites : ℝ) *
        (peeledMass (epochBase R) i : ℝ) *
        (familyWordBits wordScale R : ℝ) ≤
      16 * (updateWrites : ℝ) *
        (peeledMass (epochBase R) i : ℝ) *
        ((wordConstant wordScale : ℝ) * (logScale R : ℝ)) := by
          gcongr
    _ = ((peeledMass (epochBase R) i : ℝ) *
        (32 * (updateWrites : ℝ) * (wordConstant wordScale : ℝ) *
          (logScale R : ℝ))) / 2 := by ring
    _ ≤ ((peeledMass (epochBase R) i : ℝ) *
        (epochBase R : ℝ)) / 2 := by gcongr
    _ ≤ (epochDimension R i : ℝ) := by linarith

lemma overflow_budget_of_growth
    {updateWrites R i : ℕ} {a : ℝ}
    (hR : 6 ≤ R) (ha : 0 < a) (huw : 0 < updateWrites)
    (hi : i ∈ middleEpochs (epochCount R))
    (hgrowth :
      (logScale R : ℝ) ^ 5 ≤
        4 * a * (updateWrites : ℝ) * (epochBase R : ℝ)) :
    1 + (logScale R : ℝ) / 8 ≤
      a * sampleProbability R *
        ((updateWrites * epochDimension R i : ℕ) : ℝ) := by
  have hRone : 1 ≤ R := by omega
  have hL : 0 < (logScale R : ℝ) := by
    exact_mod_cast (show 0 < logScale R by unfold logScale; positivity)
  have hRreal : (6 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hpow : (R : ℝ) ^ 2 ≤ (R : ℝ) ^ 16 := by
    exact pow_le_pow_right₀ (by linarith) (by norm_num)
  have hL8 : (8 : ℝ) ≤ (logScale R : ℝ) := by
    rw [logScale_cast_eq_root_pow]
    nlinarith [sq_nonneg ((R : ℝ) - 6)]
  have hdimNat := epochBase_le_middle_dimension (show 2 ≤ R by omega) hi
  have hdim : (epochBase R : ℝ) ≤ (epochDimension R i : ℝ) := by
    exact_mod_cast hdimNat
  have hgrowth' :
      (logScale R : ℝ) ^ 5 ≤
        4 * a * (updateWrites : ℝ) * (epochDimension R i : ℝ) := by
    calc
      (logScale R : ℝ) ^ 5 ≤
          4 * a * (updateWrites : ℝ) * (epochBase R : ℝ) := hgrowth
      _ ≤ 4 * a * (updateWrites : ℝ) * (epochDimension R i : ℝ) := by
        gcongr
  have hquarter : (logScale R : ℝ) / 4 ≤
      (a * (updateWrites : ℝ) * (epochDimension R i : ℝ)) /
        (logScale R : ℝ) ^ 4 := by
    rw [le_div_iff₀ (pow_pos hL 4)]
    nlinarith [hgrowth']
  calc
    1 + (logScale R : ℝ) / 8 ≤ (logScale R : ℝ) / 4 := by
      linarith
    _ ≤ (a * (updateWrites : ℝ) * (epochDimension R i : ℝ)) /
        (logScale R : ℝ) ^ 4 := hquarter
    _ = a * sampleProbability R *
        ((updateWrites * epochDimension R i : ℕ) : ℝ) := by
      unfold sampleProbability samplingProbability
      push_cast
      field_simp

lemma collision_lt_eighth_of_gap
    {R i : ℕ} (hR : 6 ≤ R)
    (hi : i ∈ middleEpochs (epochCount R))
    (hgap : 3 * (logScale R : ℝ) ≤ (epochBase R : ℝ)) :
    collisionRatio R i < (1 / 8 : ℝ) := by
  have hgapNat : 3 * logScale R ≤ epochBase R := by exact_mod_cast hgap
  have hdim := epochBase_le_middle_dimension (show 2 ≤ R by omega) hi
  have hLfour : 4 ≤ logScale R := by
    have hRpow : R ≤ R ^ 16 := Nat.le_pow (by omega)
    unfold logScale
    omega
  have hexp : 3 + 2 * logScale R < epochDimension R i := by
    omega
  have hpowers :
      2 ^ (3 + 2 * logScale R) < 2 ^ epochDimension R i :=
    Nat.pow_lt_pow_right (by norm_num) hexp
  have hscaledNat :
      8 * updateCount R ^ 2 < 2 ^ epochDimension R i := by
    have heq :
        8 * updateCount R ^ 2 = 2 ^ (3 + 2 * logScale R) := by
      rw [updateCount, show 8 = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add]
      congr 1
      omega
    rw [heq]
    exact hpowers
  have hscaled :
      (8 : ℝ) * (updateCount R : ℝ) ^ 2 <
        ((2 ^ epochDimension R i : ℕ) : ℝ) := by
    exact_mod_cast hscaledNat
  have hden : 0 < ((2 ^ epochDimension R i : ℕ) : ℝ) := by positivity
  unfold collisionRatio
  rw [div_lt_iff₀ hden]
  nlinarith

lemma separation_threshold_of_root_ge_six {R : ℕ} (hR : 6 ≤ R) :
    6 < (2 : ℝ) ^ ((logScale R : ℝ) / 8) := by
  have hRreal : (6 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hpow16 : (R : ℝ) ^ 2 ≤ (R : ℝ) ^ 16 := by
    exact pow_le_pow_right₀ (by linarith) (by norm_num)
  have hL : (24 : ℝ) ≤ (logScale R : ℝ) := by
    rw [logScale_cast_eq_root_pow]
    nlinarith [sq_nonneg ((R : ℝ) - 6)]
  have hexponent : (3 : ℝ) ≤ (logScale R : ℝ) / 8 := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 2) hexponent
  have height : (8 : ℝ) ≤ (2 : ℝ) ^ ((logScale R : ℝ) / 8) := by
    calc
      (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ ((logScale R : ℝ) / 8) := hpow
  linarith

theorem certificate_of_thresholds
    {wordScale queryScale updateWrites R : ℕ} {A a : ℝ}
    (hA : 0 < A) (ha : 0 < a) (huw : 0 < updateWrites)
    (hdiv : 6 ∣ R)
    (h : ScaleThresholds wordScale queryScale updateWrites A a R) :
    ScaleCertificate wordScale queryScale updateWrites A a R := by
  have hRone : 1 ≤ R := (by omega : 1 ≤ 6).trans h.root_ge_six
  have hRtwo : 2 ≤ R := (by omega : 2 ≤ 6).trans h.root_ge_six
  have hgapNat : 3 * logScale R ≤ epochBase R := by
    exact_mod_cast h.dimension_gap
  refine
    { six_dvd := hdiv
      root_ge_six := h.root_ge_six
      geometry_power := epochBase_pow_epochCount R
      geometry_fit := geometric_epochs_fit hRone
      middle_nonempty := middleEpochs_nonempty (epochCount_ge_two hRtwo)
      word_bound := familyWordBits_le hRone wordScale
      query_bound := familyQueryReads_le hRone queryScale
      query_per_middle_epoch :=
        familyQueryReads_per_middle_le hRone hdiv queryScale
      sample_pos := sampleProbability_pos hRone
      sample_le_half := sampleProbability_le_half hRtwo
      log_inverse_bound := logInvSample_le hRone
      lambda_nonnegative := familyLambda_nonneg hRone queryScale
      lambda_bound := familyLambda_le hRone queryScale
      exponent_bound := exponent_bound_of_thresholds hA hRone
        h.exponent_polynomial
      dimension_ge_two := ?_
      dimension_ge_log := ?_
      dimension_le_five_sixths := ?_
      collision_lt_eighth := ?_
      message_cap := ?_
      overflow_budget := ?_
      separation_threshold := separation_threshold_of_root_ge_six h.root_ge_six }
  · intro i hi
    exact (epochBase_ge_two hRone).trans
      (epochBase_le_middle_dimension hRtwo hi)
  · intro i hi
    have hbase := epochBase_le_middle_dimension hRtwo hi
    omega
  · intro i hi
    exact middle_dimension_upper hi
  · intro i hi
    exact collision_lt_eighth_of_gap h.root_ge_six hi h.dimension_gap
  · intro i hi
    have hiOne := middle_index_pos hRtwo hi
    have hdNat : 8 ≤ epochDimension R i := by
      have hbase : 8 ≤ epochBase R := by
        unfold epochBase
        calc
          8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ R := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact hbase.trans (epochBase_le_middle_dimension hRtwo hi)
    have hsample := sample_message_coefficient_le_one hRone h.sampled_message
    have hcache := cached_message_coefficient_le_dimension hRone hiOne
      h.cache_message
    unfold familyMessageCost
    push_cast
    simpa only [mul_assoc] using message_sum_le_half
      (show 0 ≤ (epochDimension R i : ℝ) by positivity)
      hsample hcache (by exact_mod_cast hdNat)
  · intro i hi
    exact overflow_budget_of_growth h.root_ge_six ha huw hi h.overflow_growth

lemma eventually_const_le_pow (C : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ R : ℕ in atTop, C ≤ (R : ℝ) ^ k := by
  obtain ⟨N, hN⟩ := exists_nat_gt C
  filter_upwards [eventually_ge_atTop (max N 1)] with R hR
  have hNR : N ≤ R := le_trans (Nat.le_max_left _ _) hR
  have hRoneNat : 1 ≤ R := le_trans (Nat.le_max_right _ _) hR
  have hCR : C ≤ (R : ℝ) := by
    exact hN.le.trans (by exact_mod_cast hNR)
  have hRone : (1 : ℝ) ≤ R := by exact_mod_cast hRoneNat
  have hpow : (R : ℝ) ≤ (R : ℝ) ^ k := by
    simpa only [pow_one] using pow_le_pow_right₀ hRone hk
  exact hCR.trans hpow

theorem eventually_scaleThresholds
    (wordScale queryScale updateWrites : ℕ) (A a : ℝ)
    (ha : 0 < a) (huw : 0 < updateWrites) :
    ∀ᶠ R : ℕ in atTop,
      ScaleThresholds wordScale queryScale updateWrites A a R := by
  let Cw : ℝ := wordConstant wordScale
  let uw : ℝ := updateWrites
  let overflowCoefficient : ℝ := (4 * a * uw)⁻¹
  have hsample := eventually_const_le_pow (64 * uw * Cw) 48 (by norm_num)
  have hexponent := eventually_const_le_pow
    (8 * A * logConstant *
      (rootConstant queryScale + lambdaConstant queryScale)) 6 (by norm_num)
  have hdimension := eventually_const_mul_pow_le_two_pow 3 16
  have hcache := eventually_const_mul_pow_le_two_pow (32 * uw * Cw) 16
  have hoverflow :=
    eventually_const_mul_pow_le_two_pow overflowCoefficient 80
  filter_upwards [eventually_ge_atTop 6, hsample, hexponent,
    hdimension, hcache, hoverflow] with R hR hs he hd hc ho
  have hv : 0 < 4 * a * uw := by
    dsimp [uw]
    positivity
  have huwnz : uw ≠ 0 := by
    dsimp [uw]
    exact_mod_cast (Nat.ne_of_gt huw)
  refine
    { root_ge_six := hR
      exponent_polynomial := he
      sampled_message := ?_
      cache_message := ?_
      dimension_gap := ?_
      overflow_growth := ?_ }
  · dsimp [uw, Cw] at hs ⊢
    calc
      64 * (updateWrites : ℝ) * (wordConstant wordScale : ℝ) ≤
          (R : ℝ) ^ 48 := hs
      _ = (logScale R : ℝ) ^ 3 := by
        simp only [logScale, Nat.cast_pow]
        ring
  · dsimp [uw, Cw] at hc ⊢
    calc
      32 * (updateWrites : ℝ) * (wordConstant wordScale : ℝ) *
          (logScale R : ℝ) =
          (32 * (updateWrites : ℝ) * (wordConstant wordScale : ℝ)) *
            (R : ℝ) ^ 16 := by simp [logScale]
      _ ≤ (2 : ℝ) ^ R := hc
      _ = (epochBase R : ℝ) := by simp [epochBase]
  · calc
      3 * (logScale R : ℝ) = 3 * (R : ℝ) ^ 16 := by simp [logScale]
      _ ≤ (2 : ℝ) ^ R := hd
      _ = (epochBase R : ℝ) := by simp [epochBase]
  · have hmul := mul_le_mul_of_nonneg_left ho hv.le
    calc
      (logScale R : ℝ) ^ 5 = (R : ℝ) ^ 80 := by
        simp only [logScale, Nat.cast_pow]
        ring
      _ = (4 * a * uw) * (overflowCoefficient * (R : ℝ) ^ 80) := by
        change (R : ℝ) ^ 80 =
          (4 * a * uw) * ((4 * a * uw)⁻¹ * (R : ℝ) ^ 80)
        field_simp [ha.ne', huwnz]
      _ ≤ (4 * a * uw) * (2 : ℝ) ^ R := hmul
      _ = 4 * a * (updateWrites : ℝ) * (epochBase R : ℝ) := by
        dsimp [uw]
        simp [epochBase]

theorem exists_scaleCertificate
    (wordScale queryScale updateWrites : ℕ) (A a : ℝ)
    (hA : 0 < A) (ha : 0 < a) (huw : 0 < updateWrites) :
    ∀ Rmin : ℕ, ∃ R : ℕ,
      Rmin ≤ R ∧ ScaleCertificate wordScale queryScale updateWrites A a R := by
  intro Rmin
  have hall := eventually_scaleThresholds wordScale queryScale updateWrites
    A a ha huw
  rw [eventually_atTop] at hall
  obtain ⟨N, hN⟩ := hall
  let R : ℕ := 6 * (max N Rmin + 1)
  have hNR : N ≤ R := by
    dsimp [R]
    omega
  have hRmin : Rmin ≤ R := by
    dsimp [R]
    omega
  have hdiv : 6 ∣ R := by
    refine ⟨max N Rmin + 1, ?_⟩
    simp [R]
  exact ⟨R, hRmin,
    certificate_of_thresholds hA ha huw hdiv (hN R hNR)⟩

end PegSeparation.LowerBound.FamilyScale
