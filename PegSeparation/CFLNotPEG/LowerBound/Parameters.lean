import Mathlib


namespace PegSeparation.LowerBound.Parameters

noncomputable def samplingProbability (L : ℝ) (K : ℕ) : ℝ := (L ^ K)⁻¹

noncomputable def correctedExponent
    (A tTot Lambda logInvP : ℝ) : ℝ :=
  A * (Real.sqrt (tTot * Lambda) + Lambda) * logInvP

noncomputable def mainTerm (exponent : ℝ) : ℝ :=
  (2 : ℝ) ^ (-exponent)

noncomputable def overflowTerm (a p S : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(a * p * S))

noncomputable def coherenceQuarterBound (C L : ℝ) : ℝ :=
  C * (2 : ℝ) ^ (-(L / 4))

noncomputable def sixteenthRoot (L : ℝ) : ℝ :=
  L ^ (1 / 16 : ℝ)

lemma samplingProbability_pos {L : ℝ} (hL : 0 < L) (K : ℕ) :
    0 < samplingProbability L K := by
  exact inv_pos.mpr (pow_pos hL K)

lemma samplingProbability_nonneg {L : ℝ} (hL : 0 ≤ L) (K : ℕ) :
    0 ≤ samplingProbability L K := by
  exact inv_nonneg.mpr (pow_nonneg hL K)

lemma logb_inv_samplingProbability {L : ℝ} (_hL : 0 < L) (K : ℕ) :
    Real.logb 2 (samplingProbability L K)⁻¹ =
      (K : ℝ) * Real.logb 2 L := by
  rw [samplingProbability, inv_inv]
  exact Real.logb_pow 2 L K

lemma logb_le_sixteenth_root {L : ℝ} (hL : 0 ≤ L) :
    Real.logb 2 L ≤
      (16 / Real.log 2) * sixteenthRoot L := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hraw := Real.log_le_rpow_div hL (by norm_num : (0 : ℝ) < 1 / 16)
  rw [← Real.log_div_log]
  calc
    Real.log L / Real.log 2 ≤
        (L ^ (1 / 16 : ℝ) / (1 / 16 : ℝ)) / Real.log 2 := by
      exact div_le_div_of_nonneg_right hraw hlogTwo.le
    _ = (16 / Real.log 2) * sixteenthRoot L := by
      unfold sixteenthRoot
      field_simp

lemma sixteenthRoot_pow {L : ℝ} (hL : 0 ≤ L) :
    sixteenthRoot L ^ 16 = L := by
  simpa [sixteenthRoot, one_div] using
    Real.rpow_inv_natCast_pow hL (by norm_num : (16 : ℕ) ≠ 0)

lemma lambda_le_root_sq
    {ell r tUpd logInvP Lambda Cu K : ℝ}
    (hell : 0 ≤ ell) (hr : 1 ≤ r)
    (hCu : 0 ≤ Cu) (hK : 0 ≤ K)
    (hellr : ell ≤ r)
    (htUpd : tUpd ≤ Cu * ell)
    (hlog : logInvP = K * ell)
    (hLambda : Lambda = 1 + tUpd * logInvP) :
    Lambda ≤ (1 + Cu * K) * r ^ 2 := by
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  have htlog : tUpd * logInvP ≤ (Cu * ell) * (K * ell) := by
    rw [hlog]
    exact mul_le_mul_of_nonneg_right htUpd (mul_nonneg hK hell)
  have hellsq : ell ^ 2 ≤ r ^ 2 := by
    nlinarith
  calc
    Lambda = 1 + tUpd * logInvP := hLambda
    _ ≤ 1 + (Cu * ell) * (K * ell) := add_le_add (le_refl 1) htlog
    _ = 1 + (Cu * K) * ell ^ 2 := by ring
    _ ≤ 1 + (Cu * K) * r ^ 2 := by gcongr
    _ ≤ (1 + Cu * K) * r ^ 2 := by
      nlinarith [sq_nonneg r]

lemma sqrt_time_lambda_le
    {L r tTot Lambda Ct Clambda B : ℝ}
    (hr : 0 ≤ r)
    (hLambda0 : 0 ≤ Lambda)
    (hCt : 0 ≤ Ct) (hClambda : 0 ≤ Clambda) (hB : 0 ≤ B)
    (hL : L = r ^ 16)
    (htTot : tTot ≤ Ct * L)
    (hLambda : Lambda ≤ Clambda * r ^ 2)
    (hBsq : Ct * Clambda ≤ B ^ 2) :
    Real.sqrt (tTot * Lambda) ≤ B * r ^ 9 := by
  have htimeCap0 : 0 ≤ Ct * L := by
    rw [hL]
    positivity
  have hlambdaCap0 : 0 ≤ Clambda * r ^ 2 := by positivity
  have hprod : tTot * Lambda ≤ (Ct * L) * (Clambda * r ^ 2) := by
    exact mul_le_mul htTot hLambda hLambda0 htimeCap0
  have hprod' : tTot * Lambda ≤ B ^ 2 * r ^ 18 := by
    calc
      tTot * Lambda ≤ (Ct * L) * (Clambda * r ^ 2) := hprod
      _ = (Ct * Clambda) * r ^ 18 := by rw [hL]; ring
      _ ≤ B ^ 2 * r ^ 18 := by gcongr
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      tTot * Lambda ≤ B ^ 2 * r ^ 18 := hprod'
      _ = (B * r ^ 9) ^ 2 := by ring

theorem correctedExponent_le_log_eighth
    {A L r tTot Lambda logInvP Ct Clambda B K : ℝ}
    (hA : 0 ≤ A) (hr : 1 ≤ r)
    (hLambda0 : 0 ≤ Lambda)
    (hlog0 : 0 ≤ logInvP)
    (hCt : 0 ≤ Ct) (hClambda : 0 ≤ Clambda)
    (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hL : L = r ^ 16)
    (htTot : tTot ≤ Ct * L)
    (hLambda : Lambda ≤ Clambda * r ^ 2)
    (hlog : logInvP ≤ K * r)
    (hBsq : Ct * Clambda ≤ B ^ 2)
    (hthreshold : 8 * A * K * (B + Clambda) ≤ r ^ 6) :
    correctedExponent A tTot Lambda logInvP ≤ L / 8 := by
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  have hsqrt := sqrt_time_lambda_le hr0 hLambda0 hCt hClambda hB
    hL htTot hLambda hBsq
  have hsum : Real.sqrt (tTot * Lambda) + Lambda ≤
      B * r ^ 9 + Clambda * r ^ 2 := add_le_add hsqrt hLambda
  have hfirst : correctedExponent A tTot Lambda logInvP ≤
      A * (B * r ^ 9 + Clambda * r ^ 2) * (K * r) := by
    unfold correctedExponent
    gcongr
  have hrpow : r ^ 3 ≤ r ^ 10 := by
    exact pow_le_pow_right₀ hr (by norm_num)
  have hcoarse :
      A * (B * r ^ 9 + Clambda * r ^ 2) * (K * r) ≤
        A * K * (B + Clambda) * r ^ 10 := by
    have hinner : B * r ^ 10 + Clambda * r ^ 3 ≤
        (B + Clambda) * r ^ 10 := by
      nlinarith [mul_le_mul_of_nonneg_left hrpow hClambda]
    calc
      A * (B * r ^ 9 + Clambda * r ^ 2) * (K * r) =
          A * K * (B * r ^ 10 + Clambda * r ^ 3) := by ring
      _ ≤ A * K * ((B + Clambda) * r ^ 10) := by gcongr
      _ = A * K * (B + Clambda) * r ^ 10 := by ring
  have hscaled := mul_le_mul_of_nonneg_right hthreshold (pow_nonneg hr0 10)
  have hlast : A * K * (B + Clambda) * r ^ 10 ≤ r ^ 16 / 8 := by
    have hpow : r ^ 6 * r ^ 10 = r ^ 16 := by ring
    rw [hpow] at hscaled
    nlinarith
  calc
    correctedExponent A tTot Lambda logInvP ≤
        A * (B * r ^ 9 + Clambda * r ^ 2) * (K * r) := hfirst
    _ ≤ A * K * (B + Clambda) * r ^ 10 := hcoarse
    _ ≤ r ^ 16 / 8 := hlast
    _ = L / 8 := by rw [hL]

lemma mainTerm_ge_log_eighth {exponent L : ℝ} (h : exponent ≤ L / 8) :
    (2 : ℝ) ^ (-(L / 8)) ≤ mainTerm exponent := by
  unfold mainTerm
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

lemma overflowTerm_le_half_log_eighth
    {a p S L : ℝ} (h : 1 + L / 8 ≤ a * p * S) :
    overflowTerm a p S ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(L / 8)) := by
  have hmono : (2 : ℝ) ^ (-(a * p * S)) ≤
      (2 : ℝ) ^ (-(1 + L / 8)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc
    overflowTerm a p S = (2 : ℝ) ^ (-(a * p * S)) := rfl
    _ ≤ (2 : ℝ) ^ (-(1 + L / 8)) := hmono
    _ = (1 / 2 : ℝ) * (2 : ℝ) ^ (-(L / 8)) := by
      rw [show -(1 + L / 8) = (-1 : ℝ) + (-(L / 8)) by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num [Real.rpow_neg_one]

lemma sampling_mass_lower
    {L d nThird tUpd : ℝ} (B K : ℕ)
    (hL : 0 < L) (hd0 : 0 ≤ d) (_hnThird : 0 ≤ nThird)
    (hd : nThird / L ^ B ≤ d) (htUpd : 1 ≤ tUpd) :
    nThird / L ^ (B + K) ≤
      samplingProbability L K * (tUpd * d) := by
  have hp0 : 0 ≤ samplingProbability L K :=
    (samplingProbability_pos hL K).le
  have htd : d ≤ tUpd * d := by nlinarith
  have hdenB : L ^ B ≠ 0 := (pow_pos hL B).ne'
  have hdenK : L ^ K ≠ 0 := (pow_pos hL K).ne'
  have heq : samplingProbability L K * (nThird / L ^ B) =
      nThird / L ^ (B + K) := by
    rw [samplingProbability, pow_add]
    field_simp
  calc
    nThird / L ^ (B + K) =
        samplingProbability L K * (nThird / L ^ B) := heq.symm
    _ ≤ samplingProbability L K * d := by gcongr
    _ ≤ samplingProbability L K * (tUpd * d) := by gcongr

lemma log_scale_le_dimension
    {L d nThird : ℝ} (B : ℕ)
    (hL : 0 < L)
    (hd : nThird / L ^ B ≤ d)
    (hthreshold : L ^ (B + 1) ≤ nThird) :
    L ≤ d := by
  have hden : 0 ≤ L ^ B := (pow_pos hL B).le
  have heq : L = L ^ (B + 1) / L ^ B := by
    rw [pow_succ]
    field_simp
  calc
    L = L ^ (B + 1) / L ^ B := heq
    _ ≤ nThird / L ^ B := div_le_div_of_nonneg_right hthreshold hden
    _ ≤ d := hd

lemma overflow_budget_from_dimension
    {L d nThird tUpd a : ℝ} (B K : ℕ)
    (hL : 0 < L) (hd0 : 0 ≤ d) (hnThird : 0 ≤ nThird)
    (ha : 0 ≤ a)
    (hd : nThird / L ^ B ≤ d) (htUpd : 1 ≤ tUpd)
    (hthreshold :
      1 + L / 8 ≤ a * (nThird / L ^ (B + K))) :
    1 + L / 8 ≤
      a * samplingProbability L K * (tUpd * d) := by
  have hmass := sampling_mass_lower B K hL hd0 hnThird hd htUpd
  have hscaled := mul_le_mul_of_nonneg_left hmass ha
  nlinarith

lemma dimension_ratio_quarter_le
    {n d : ℝ} (hn : 1 ≤ n) (hd0 : 0 ≤ d)
    (hd : d ≤ n ^ (5 / 6 : ℝ)) :
    (d / n ^ 2) ^ (1 / 4 : ℝ) ≤ n ^ (-(1 / 4 : ℝ)) := by
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hfive : n ^ (5 / 6 : ℝ) ≤ n := by
    calc
      n ^ (5 / 6 : ℝ) ≤ n ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
      _ = n := Real.rpow_one n
  have hdn : d ≤ n := hd.trans hfive
  have hdiv : d / n ^ 2 ≤ n / n ^ 2 := by
    exact div_le_div_of_nonneg_right hdn (sq_nonneg n)
  have hratio0 : 0 ≤ d / n ^ 2 := div_nonneg hd0 (sq_nonneg n)
  have hrpow := Real.rpow_le_rpow hratio0 hdiv (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hratio : n / n ^ 2 = n⁻¹ := by
    field_simp
  calc
    (d / n ^ 2) ^ (1 / 4 : ℝ) ≤ (n / n ^ 2) ^ (1 / 4 : ℝ) := hrpow
    _ = n⁻¹ ^ (1 / 4 : ℝ) := by rw [hratio]
    _ = (n ^ (1 / 4 : ℝ))⁻¹ := Real.inv_rpow hn0 _
    _ = n ^ (-(1 / 4 : ℝ)) := (Real.rpow_neg hn0 _).symm

lemma exponential_dimension_term_le
    {n L d : ℝ} (hscale : n = (2 : ℝ) ^ L) (hd : L ≤ d) :
    (2 : ℝ) ^ (-(d / 4)) ≤ n ^ (-(1 / 4 : ℝ)) := by
  have hmono : (2 : ℝ) ^ (-(d / 4)) ≤ (2 : ℝ) ^ (-(L / 4)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc
    (2 : ℝ) ^ (-(d / 4)) ≤ (2 : ℝ) ^ (-(L / 4)) := hmono
    _ = ((2 : ℝ) ^ L) ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    _ = n ^ (-(1 / 4 : ℝ)) := by rw [hscale]

lemma coherence_components_le_quarter
    {n L d C : ℝ}
    (hn : 1 ≤ n) (hd0 : 0 ≤ d) (hC : 0 ≤ C)
    (hscale : n = (2 : ℝ) ^ L)
    (hdLower : L ≤ d)
    (hdUpper : d ≤ n ^ (5 / 6 : ℝ)) :
    (2 : ℝ) ^ (-(d / 4)) + C * (d / n ^ 2) ^ (1 / 4 : ℝ) ≤
      coherenceQuarterBound (1 + C) L := by
  have hexp := exponential_dimension_term_le hscale hdLower
  have hratio := dimension_ratio_quarter_le hn hd0 hdUpper
  have hsum :
      (2 : ℝ) ^ (-(d / 4)) + C * (d / n ^ 2) ^ (1 / 4 : ℝ) ≤
        (1 + C) * n ^ (-(1 / 4 : ℝ)) := by
    calc
      (2 : ℝ) ^ (-(d / 4)) + C * (d / n ^ 2) ^ (1 / 4 : ℝ) ≤
          n ^ (-(1 / 4 : ℝ)) + C * n ^ (-(1 / 4 : ℝ)) := by
            exact add_le_add hexp (mul_le_mul_of_nonneg_left hratio hC)
      _ = (1 + C) * n ^ (-(1 / 4 : ℝ)) := by ring
  calc
    (2 : ℝ) ^ (-(d / 4)) + C * (d / n ^ 2) ^ (1 / 4 : ℝ) ≤
        (1 + C) * n ^ (-(1 / 4 : ℝ)) := hsum
    _ = coherenceQuarterBound (1 + C) L := by
      unfold coherenceQuarterBound
      rw [hscale, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 2
      ring

lemma coherenceQuarter_lt_half_log_eighth
    {C L : ℝ} (_hC : 0 ≤ C)
    (hthreshold : 2 * C < (2 : ℝ) ^ (L / 8)) :
    coherenceQuarterBound C L <
      (1 / 2 : ℝ) * (2 : ℝ) ^ (-(L / 8)) := by
  let x : ℝ := (2 : ℝ) ^ (L / 8)
  have hx : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  have hquarter : (2 : ℝ) ^ (L / 4) = x ^ 2 := by
    dsimp [x]
    rw [show L / 4 = L / 8 + L / 8 by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring
  have hnegEighth : (2 : ℝ) ^ (-(L / 8)) = x⁻¹ := by
    dsimp [x]
    exact Real.rpow_neg (by norm_num) _
  have hnegQuarter : (2 : ℝ) ^ (-(L / 4)) = (x ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), hquarter]
  rw [coherenceQuarterBound, hnegQuarter, hnegEighth]
  have hmul : C * (2 * x) < 1 * x ^ 2 := by
    change 2 * C < x at hthreshold
    nlinarith [mul_pos hx (sub_pos.mpr hthreshold)]
  have hden1 : 0 < x ^ 2 := sq_pos_of_pos hx
  have hden2 : 0 < 2 * x := mul_pos (by norm_num) hx
  rw [show C * (x ^ 2)⁻¹ = C / (x ^ 2) by ring,
    show (1 / 2 : ℝ) * x⁻¹ = 1 / (2 * x) by field_simp]
  exact (div_lt_div_iff₀ hden1 hden2).2 hmul

theorem no_advantage_between_bounds
    {adv exponent a p S C L : ℝ}
    (hC : 0 ≤ C)
    (hexponent : exponent ≤ L / 8)
    (hoverflow : 1 + L / 8 ≤ a * p * S)
    (hthreshold : 2 * C < (2 : ℝ) ^ (L / 8))
    (hLower : mainTerm exponent - overflowTerm a p S ≤ adv)
    (hUpper : adv ≤ coherenceQuarterBound C L) : False := by
  have hmain := mainTerm_ge_log_eighth hexponent
  have htail := overflowTerm_le_half_log_eighth hoverflow
  have hgap := coherenceQuarter_lt_half_log_eighth hC hthreshold
  linarith

theorem no_advantage_between_dimension_bounds
    {adv exponent a p S C n L d : ℝ}
    (hn : 1 ≤ n) (hd0 : 0 ≤ d) (hC : 0 ≤ C)
    (hscale : n = (2 : ℝ) ^ L)
    (hdLower : L ≤ d)
    (hdUpper : d ≤ n ^ (5 / 6 : ℝ))
    (hexponent : exponent ≤ L / 8)
    (hoverflow : 1 + L / 8 ≤ a * p * S)
    (hthreshold : 2 * (1 + C) < (2 : ℝ) ^ (L / 8))
    (hLower : mainTerm exponent - overflowTerm a p S ≤ adv)
    (hUpper :
      adv ≤ (2 : ℝ) ^ (-(d / 4)) +
        C * (d / n ^ 2) ^ (1 / 4 : ℝ)) : False := by
  have hcomponents :=
    coherence_components_le_quarter hn hd0 hC hscale hdLower hdUpper
  exact no_advantage_between_bounds (by positivity : 0 ≤ 1 + C)
    hexponent hoverflow hthreshold hLower (hUpper.trans hcomponents)

theorem no_advantage_for_corrected_simulation
    {adv A L r tTot Lambda logInvP Ct Clambda B K a p S C : ℝ}
    (hA : 0 ≤ A) (hr : 1 ≤ r)
    (hLambda0 : 0 ≤ Lambda)
    (hlog0 : 0 ≤ logInvP)
    (hCt : 0 ≤ Ct) (hClambda : 0 ≤ Clambda)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hL : L = r ^ 16)
    (htTot : tTot ≤ Ct * L)
    (hLambda : Lambda ≤ Clambda * r ^ 2)
    (hlog : logInvP ≤ K * r)
    (hBsq : Ct * Clambda ≤ B ^ 2)
    (hexponentThreshold : 8 * A * K * (B + Clambda) ≤ r ^ 6)
    (hoverflow : 1 + L / 8 ≤ a * p * S)
    (hcoherenceThreshold : 2 * C < (2 : ℝ) ^ (L / 8))
    (hLower :
      mainTerm (correctedExponent A tTot Lambda logInvP) -
          overflowTerm a p S ≤ adv)
    (hUpper : adv ≤ coherenceQuarterBound C L) : False := by
  apply no_advantage_between_bounds hC
    (correctedExponent_le_log_eighth hA hr hLambda0 hlog0 hCt
      hClambda hB hK hL htTot hLambda hlog hBsq hexponentThreshold)
    hoverflow hcoherenceThreshold hLower hUpper

end PegSeparation.LowerBound.Parameters
