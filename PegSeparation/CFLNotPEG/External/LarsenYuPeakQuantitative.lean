import PegSeparation.CFLNotPEG.External.PeakToAverageBounds
import PegSeparation.CFLNotPEG.External.PeakToAverageChebyshev
import Mathlib.Analysis.Complex.ExponentialBounds


open scoped BigOperators

namespace PegSeparation.External.LarsenYuPeakQuantitative

noncomputable section

open PeakToAverage
open PeakToAverageBounds
open PeakToAverageChebyshev

def peakScale (baseline : ℝ) : ℝ := 2 / baseline

def peakDegreeBudget (k cutoff : Nat) (baseline : ℝ) : Nat :=
  appendixMainDegree k cutoff (peakScale baseline) +
    ∑ i ∈ Finset.Ico 1 cutoff, appendixCorrectionDegree k i

theorem exists_fiberL1_ge_inv_nine_pow_peakDegreeBudget
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k cutoff : Nat} {baseline : ℝ}
    (ht : 0 < cutoff) (htwo : 2 * cutoff ≤ k)
    (hbaseline : 0 < baseline)
    (f : (Fin k → Alphabet) → ℝ) (peak : Fin k → Alphabet)
    (hfL1 : ∑ point, |f point| ≤ 1)
    (hfpeak : baseline ≤ |f peak|) :
    ∃ coordinates : Finset (Fin k),
      coordinates.card ≤ peakDegreeBudget k cutoff baseline ∧
        1 / (9 : ℝ) ^ peakDegreeBudget k cutoff baseline ≤
          fiberL1 f coordinates := by
  have hscalePositive : 0 < peakScale baseline := by
    unfold peakScale
    positivity
  let certificate :=
    explicitAppendixCertificate ht htwo hscalePositive
  have hcoefficient :
      certificate.coefficientL1 ≤
        (9 : ℝ) ^ peakDegreeBudget k cutoff baseline := by
    dsimp [certificate, peakDegreeBudget]
    exact explicitAppendixCertificate_coefficientL1_le_nine_pow
      ht htwo hscalePositive
  have hboundPositive :
      0 < (9 : ℝ) ^ peakDegreeBudget k cutoff baseline := by positivity
  have hscale : 2 ≤ peakScale baseline * baseline := by
    rw [peakScale, div_mul_cancel₀ (2 : ℝ) (ne_of_gt hbaseline)]
  obtain ⟨coordinates, hdegree, hfiber⟩ :=
    exists_fiberL1_ge_inv_of_certificate certificate hcoefficient
      hboundPositive f peak hbaseline hfL1 hfpeak hscale
  refine ⟨coordinates, ?_, hfiber⟩
  exact hdegree.trans (by
    dsimp [certificate, peakDegreeBudget]
    exact natDegree_chosenAppendixPolynomial_le k cutoff (peakScale baseline))

theorem exists_fiberL1_ge_nine_rpow_neg_peakDegreeBudget
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k cutoff : Nat} {baseline : ℝ}
    (ht : 0 < cutoff) (htwo : 2 * cutoff ≤ k)
    (hbaseline : 0 < baseline)
    (f : (Fin k → Alphabet) → ℝ) (peak : Fin k → Alphabet)
    (hfL1 : ∑ point, |f point| ≤ 1)
    (hfpeak : baseline ≤ |f peak|) :
    ∃ coordinates : Finset (Fin k),
      coordinates.card ≤ peakDegreeBudget k cutoff baseline ∧
        Real.rpow 9 (-(peakDegreeBudget k cutoff baseline : ℝ)) ≤
          fiberL1 f coordinates := by
  obtain ⟨coordinates, hdegree, hfiber⟩ :=
    exists_fiberL1_ge_inv_nine_pow_peakDegreeBudget
      ht htwo hbaseline f peak hfL1 hfpeak
  refine ⟨coordinates, hdegree, ?_⟩
  calc
    Real.rpow 9 (-(peakDegreeBudget k cutoff baseline : ℝ)) =
        1 / (9 : ℝ) ^ peakDegreeBudget k cutoff baseline := by
      rw [Real.rpow_eq_pow,
        Real.rpow_neg (x := (9 : ℝ)) (by norm_num),
        Real.rpow_natCast]
      simp [one_div]
    _ ≤ fiberL1 f coordinates := hfiber


def larsenCutoff (height logFactor : ℝ) : Nat :=
  ⌈height * logFactor⌉₊

theorem sqrt_div_mul_le_sqrt_mul
    {dimension height cutoff : ℝ}
    (hdimension : 0 ≤ dimension) (hheight : 0 < height)
    (hheightCutoff : height ≤ cutoff) :
    Real.sqrt (dimension / cutoff) * height ≤
      Real.sqrt (dimension * height) := by
  have hcutoffPositive : 0 < cutoff := hheight.trans_le hheightCutoff
  have hsqrtCutoffPositive : 0 < Real.sqrt cutoff :=
    Real.sqrt_pos.2 hcutoffPositive
  have hsqrtHeightCutoff : Real.sqrt height ≤ Real.sqrt cutoff :=
    Real.sqrt_le_sqrt hheightCutoff
  have hheightSquare :
      Real.sqrt height * Real.sqrt height = height :=
    Real.mul_self_sqrt hheight.le
  have hquotient : height / Real.sqrt cutoff ≤ Real.sqrt height := by
    apply (div_le_iff₀ hsqrtCutoffPositive).2
    calc
      height = Real.sqrt height * Real.sqrt height := hheightSquare.symm
      _ ≤ Real.sqrt height * Real.sqrt cutoff :=
        mul_le_mul_of_nonneg_left hsqrtHeightCutoff (Real.sqrt_nonneg _)
  rw [Real.sqrt_div hdimension, Real.sqrt_mul hdimension]
  calc
    Real.sqrt dimension / Real.sqrt cutoff * height =
        Real.sqrt dimension * (height / Real.sqrt cutoff) := by ring
    _ ≤ Real.sqrt dimension * Real.sqrt height :=
      mul_le_mul_of_nonneg_left hquotient (Real.sqrt_nonneg _)

theorem cast_peakDegreeBudget_larsenCutoff_le
    {k : Nat} {baseline height logFactor : ℝ}
    (hbaseline : 0 < baseline) (hbaselineOne : baseline ≤ 1)
    (hheight : 1 ≤ height) (hlogFactor : 1 ≤ logFactor)
    (hpeakHeight : Real.log (4 / baseline) ≤ height * logFactor)
    (hvalid : 2 * larsenCutoff height logFactor ≤ k) :
    (peakDegreeBudget k (larsenCutoff height logFactor) baseline : ℝ) ≤
      12 * (Real.sqrt ((k : ℝ) * height) + height) * logFactor := by
  let totalHeight : ℝ := height * logFactor
  let cutoff : Nat := larsenCutoff height logFactor
  have htotalOne : 1 ≤ totalHeight := by
    dsimp [totalHeight]
    have hmul := mul_le_mul hheight hlogFactor (by norm_num) (by linarith)
    nlinarith
  have htotalPositive : 0 < totalHeight := lt_of_lt_of_le zero_lt_one htotalOne
  have hcutoffLower : totalHeight ≤ (cutoff : ℝ) := by
    dsimp [cutoff, larsenCutoff]
    exact Nat.le_ceil totalHeight
  have hcutoffPositive : 0 < cutoff := by
    have : (1 : ℝ) ≤ (cutoff : ℝ) := htotalOne.trans hcutoffLower
    exact_mod_cast this
  have hcutoffUpper : (cutoff : ℝ) ≤ 2 * totalHeight := by
    have hceil := (Nat.ceil_lt_add_one htotalPositive.le).le
    dsimp [cutoff, larsenCutoff]
    linarith
  have hscaleOne : 1 ≤ peakScale baseline := by
    rw [peakScale, le_div_iff₀ hbaseline]
    linarith
  have hlogScale :
      Real.log (2 * peakScale baseline) ≤ totalHeight := by
    calc
      Real.log (2 * peakScale baseline) = Real.log (4 / baseline) := by
        congr 1
        simp [peakScale]
        ring
      _ ≤ height * logFactor := hpeakHeight
      _ = totalHeight := rfl
  have hbudget :
      (peakDegreeBudget k cutoff baseline : ℝ) ≤
        Real.sqrt ((k : ℝ) / (cutoff : ℝ)) *
            Real.log (2 * peakScale baseline) +
          4 * Real.sqrt ((k : ℝ) * (cutoff : ℝ)) +
          (cutoff : ℝ) + 1 := by
    simpa [peakDegreeBudget] using
      (cast_appendixDegreeBudget_le hcutoffPositive
        (by simpa [cutoff] using hvalid) hscaleOne)
  have hmain :
      Real.sqrt ((k : ℝ) / (cutoff : ℝ)) *
          Real.log (2 * peakScale baseline) ≤
        Real.sqrt ((k : ℝ) * totalHeight) := by
    calc
      Real.sqrt ((k : ℝ) / (cutoff : ℝ)) *
          Real.log (2 * peakScale baseline) ≤
          Real.sqrt ((k : ℝ) / (cutoff : ℝ)) * totalHeight :=
        mul_le_mul_of_nonneg_left hlogScale (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt ((k : ℝ) * totalHeight) :=
        sqrt_div_mul_le_sqrt_mul (Nat.cast_nonneg k) htotalPositive hcutoffLower
  have hdimensionHeight : 0 ≤ (k : ℝ) * totalHeight :=
    mul_nonneg (Nat.cast_nonneg k) htotalPositive.le
  have hcorrection :
      4 * Real.sqrt ((k : ℝ) * (cutoff : ℝ)) ≤
        8 * Real.sqrt ((k : ℝ) * totalHeight) := by
    have hfirst :
        (k : ℝ) * (cutoff : ℝ) ≤ (k : ℝ) * (2 * totalHeight) :=
      mul_le_mul_of_nonneg_left hcutoffUpper (Nat.cast_nonneg k)
    have hsecond :
        (k : ℝ) * (2 * totalHeight) ≤
          4 * ((k : ℝ) * totalHeight) := by
      nlinarith
    have hsqrt :
        Real.sqrt ((k : ℝ) * (cutoff : ℝ)) ≤
          2 * Real.sqrt ((k : ℝ) * totalHeight) := by
      calc
        Real.sqrt ((k : ℝ) * (cutoff : ℝ)) ≤
            Real.sqrt (4 * ((k : ℝ) * totalHeight)) :=
          Real.sqrt_le_sqrt (hfirst.trans hsecond)
        _ = 2 * Real.sqrt ((k : ℝ) * totalHeight) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
          norm_num
    nlinarith
  have htail : (cutoff : ℝ) + 1 ≤ 3 * totalHeight := by
    linarith
  have hrough :
      (peakDegreeBudget k cutoff baseline : ℝ) ≤
        9 * Real.sqrt ((k : ℝ) * totalHeight) + 3 * totalHeight := by
    linarith
  have hheightNonnegative : 0 ≤ height := by linarith
  have hlogFactorNonnegative : 0 ≤ logFactor := by linarith
  have hroot :
      Real.sqrt ((k : ℝ) * totalHeight) ≤
        Real.sqrt ((k : ℝ) * height) * logFactor := by
    have hbaseNonnegative : 0 ≤ (k : ℝ) * height :=
      mul_nonneg (Nat.cast_nonneg k) hheightNonnegative
    have hsqrtFactor : Real.sqrt logFactor ≤ logFactor := by
      rw [Real.sqrt_le_left hlogFactorNonnegative]
      nlinarith
    dsimp [totalHeight]
    rw [show (k : ℝ) * (height * logFactor) =
        ((k : ℝ) * height) * logFactor by ring,
      Real.sqrt_mul hbaseNonnegative]
    exact mul_le_mul_of_nonneg_left hsqrtFactor (Real.sqrt_nonneg _)
  calc
    (peakDegreeBudget k (larsenCutoff height logFactor) baseline : ℝ) =
        (peakDegreeBudget k cutoff baseline : ℝ) := by rfl
    _ ≤ 9 * Real.sqrt ((k : ℝ) * totalHeight) + 3 * totalHeight := hrough
    _ ≤ 9 * (Real.sqrt ((k : ℝ) * height) * logFactor) +
        3 * (height * logFactor) := by gcongr
    _ ≤ 12 * (Real.sqrt ((k : ℝ) * height) + height) * logFactor := by
      have hsqrtNonnegative : 0 ≤ Real.sqrt ((k : ℝ) * height) :=
        Real.sqrt_nonneg _
      nlinarith [mul_nonneg hsqrtNonnegative hlogFactorNonnegative,
        mul_nonneg hheightNonnegative hlogFactorNonnegative]

def larsenFiberReward (k : Nat) (height logFactor : ℝ) : ℝ :=
  Real.rpow 2
    (-48 * (Real.sqrt ((k : ℝ) * height) + height) * logFactor)

theorem larsenFiberReward_le_baseline
    {k : Nat} {baseline height logFactor : ℝ}
    (hbaseline : 0 < baseline)
    (hheight : 1 ≤ height) (hlogFactor : 1 ≤ logFactor)
    (hpeakHeight : Real.log (4 / baseline) ≤ height * logFactor) :
    larsenFiberReward k height logFactor ≤ baseline := by
  let totalHeight := height * logFactor
  let exponentSize :=
    48 * (Real.sqrt ((k : ℝ) * height) + height) * logFactor
  have hheightNonnegative : 0 ≤ height := by linarith
  have hlogFactorNonnegative : 0 ≤ logFactor := by linarith
  have hlogTwo : 1 ≤ 48 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hshape :
      totalHeight ≤
        (Real.sqrt ((k : ℝ) * height) + height) * logFactor := by
    dsimp [totalHeight]
    have hsqrt : 0 ≤ Real.sqrt ((k : ℝ) * height) := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hsqrt hlogFactorNonnegative]
  have hsize : totalHeight ≤ Real.log 2 * exponentSize := by
    dsimp [exponentSize]
    have hshapeNonnegative :
        0 ≤ (Real.sqrt ((k : ℝ) * height) + height) * logFactor := by
      positivity
    have hscaled :
        (Real.sqrt ((k : ℝ) * height) + height) * logFactor ≤
          (48 * Real.log 2) *
            ((Real.sqrt ((k : ℝ) * height) + height) * logFactor) :=
      by simpa using mul_le_mul_of_nonneg_right hlogTwo hshapeNonnegative
    nlinarith
  have hrewardExp : larsenFiberReward k height logFactor ≤
      Real.exp (-totalHeight) := by
    rw [larsenFiberReward, Real.rpow_eq_pow,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    dsimp [exponentSize] at hsize
    dsimp [totalHeight]
    nlinarith
  have hratio : 4 / baseline ≤ Real.exp totalHeight := by
    calc
      4 / baseline = Real.exp (Real.log (4 / baseline)) := by
        rw [Real.exp_log]
        positivity
      _ ≤ Real.exp (height * logFactor) := Real.exp_le_exp.mpr hpeakHeight
      _ = Real.exp totalHeight := by rfl
  have hfour : (4 : ℝ) ≤ Real.exp totalHeight * baseline := by
    calc
      (4 : ℝ) = (4 / baseline) * baseline := by
        field_simp
      _ ≤ Real.exp totalHeight * baseline :=
        mul_le_mul_of_nonneg_right hratio hbaseline.le
  have hexpBaseline : Real.exp (-totalHeight) ≤ baseline := by
    rw [Real.exp_neg]
    rw [← one_div]
    apply (div_le_iff₀ (Real.exp_pos totalHeight)).2
    nlinarith
  exact hrewardExp.trans hexpBaseline

theorem exists_fiberL1_larsenCutoff_uniform
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} {baseline height logFactor : ℝ}
    (hbaseline : 0 < baseline) (hbaselineOne : baseline ≤ 1)
    (hheight : 1 ≤ height) (hlogFactor : 1 ≤ logFactor)
    (hpeakHeight : Real.log (4 / baseline) ≤ height * logFactor)
    (f : (Fin k → Alphabet) → ℝ) (peak : Fin k → Alphabet)
    (hfL1 : ∑ point, |f point| ≤ 1)
    (hfpeak : baseline ≤ |f peak|) :
    ∃ coordinates : Finset (Fin k),
      (coordinates.card : ℝ) ≤
          12 * (Real.sqrt ((k : ℝ) * height) + height) * logFactor ∧
        larsenFiberReward k height logFactor ≤ fiberL1 f coordinates := by
  let cutoff := larsenCutoff height logFactor
  let degreeBudget := peakDegreeBudget k cutoff baseline
  have hheightNonnegative : 0 ≤ height := by linarith
  have hlogFactorNonnegative : 0 ≤ logFactor := by linarith
  have hrewardBaseline : larsenFiberReward k height logFactor ≤ baseline :=
    larsenFiberReward_le_baseline hbaseline hheight hlogFactor hpeakHeight
  have htotalOne : 1 ≤ height * logFactor := by
    have hmul := mul_le_mul hheight hlogFactor (by norm_num) (by linarith)
    nlinarith
  have hcutoffLower : height * logFactor ≤ (cutoff : ℝ) := by
    dsimp [cutoff, larsenCutoff]
    exact Nat.le_ceil (height * logFactor)
  have hcutoffPositive : 0 < cutoff := by
    have : (1 : ℝ) ≤ (cutoff : ℝ) := htotalOne.trans hcutoffLower
    exact_mod_cast this
  have hcutoffUpper : (cutoff : ℝ) ≤ 2 * (height * logFactor) := by
    have hceil :=
      (Nat.ceil_lt_add_one (show 0 ≤ height * logFactor by positivity)).le
    dsimp [cutoff, larsenCutoff]
    linarith
  by_cases hvalid : 2 * cutoff ≤ k
  · obtain ⟨coordinates, hcard, hfiber⟩ :=
      exists_fiberL1_ge_nine_rpow_neg_peakDegreeBudget
        hcutoffPositive hvalid hbaseline f peak hfL1 hfpeak
    have hdegreeReal : (degreeBudget : ℝ) ≤
        12 * (Real.sqrt ((k : ℝ) * height) + height) * logFactor := by
      dsimp [degreeBudget, cutoff]
      exact cast_peakDegreeBudget_larsenCutoff_le hbaseline hbaselineOne
        hheight hlogFactor hpeakHeight hvalid
    have hcardReal : (coordinates.card : ℝ) ≤
        12 * (Real.sqrt ((k : ℝ) * height) + height) * logFactor := by
      have : (coordinates.card : ℝ) ≤ (degreeBudget : ℝ) := by
        exact_mod_cast hcard
      exact this.trans hdegreeReal
    have hfactorNonnegative :
        0 ≤ (Real.sqrt ((k : ℝ) * height) + height) * logFactor := by
      positivity
    have hexponent :
        -48 * (Real.sqrt ((k : ℝ) * height) + height) * logFactor ≤
          -4 * (degreeBudget : ℝ) := by
      nlinarith
    have htwoDegree :
        Real.rpow 2
            (-48 * (Real.sqrt ((k : ℝ) * height) + height) * logFactor) ≤
          Real.rpow 2 (-4 * (degreeBudget : ℝ)) := by
      rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
    have hbaseChange :
        Real.rpow 2 (-4 * (degreeBudget : ℝ)) =
          Real.rpow 16 (-(degreeBudget : ℝ)) := by
      rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
      calc
        (2 : ℝ) ^ (-4 * (degreeBudget : ℝ)) =
            (2 : ℝ) ^ (4 * (-(degreeBudget : ℝ))) := by
          congr 1
          ring
        _ = ((2 : ℝ) ^ (4 : ℝ)) ^ (-(degreeBudget : ℝ)) := by
          rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        _ = (16 : ℝ) ^ (-(degreeBudget : ℝ)) := by norm_num
    have hnine :
        Real.rpow 16 (-(degreeBudget : ℝ)) ≤
          Real.rpow 9 (-(degreeBudget : ℝ)) := by
      rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by norm_num)
        (neg_nonpos.mpr (Nat.cast_nonneg degreeBudget))
    refine ⟨coordinates, hcardReal, ?_⟩
    change Real.rpow 2
        (-48 * (Real.sqrt ((k : ℝ) * height) + height) * logFactor) ≤
      fiberL1 f coordinates
    exact htwoDegree.trans (hbaseChange.le.trans (hnine.trans hfiber))
  · obtain ⟨coordinates, hcard, hfiber⟩ :=
      exists_full_fiberL1_ge_peak f peak hfpeak
    have hkCutoff : k < 2 * cutoff := by omega
    have hkReal : (k : ℝ) < 2 * (cutoff : ℝ) := by exact_mod_cast hkCutoff
    have hkHeight : (k : ℝ) ≤
        12 * (Real.sqrt ((k : ℝ) * height) + height) * logFactor := by
      have hsqrtNonnegative : 0 ≤ Real.sqrt ((k : ℝ) * height) :=
        Real.sqrt_nonneg _
      have hheightLogNonnegative : 0 ≤ height * logFactor :=
        mul_nonneg hheightNonnegative hlogFactorNonnegative
      have hfour : (k : ℝ) < 4 * (height * logFactor) := by linarith
      have htwelve :
          4 * (height * logFactor) ≤
            12 * (Real.sqrt ((k : ℝ) * height) + height) * logFactor := by
        nlinarith [mul_nonneg hsqrtNonnegative hlogFactorNonnegative]
      exact hfour.le.trans htwelve
    refine ⟨coordinates, ?_, hrewardBaseline.trans hfiber⟩
    have : (coordinates.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hcard
    exact this.trans hkHeight


def samplingLogFactor (p : ℝ) : ℝ := log₂ (1 / p)

def samplingLambda (updated p : ℝ) : ℝ :=
  1 + updated * samplingLogFactor p

def samplingPeakBaseline (updated p : ℝ) : ℝ :=
  Real.rpow p (4 * updated) / 4

theorem one_le_samplingLogFactor
    {p : ℝ} (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    1 ≤ samplingLogFactor p := by
  have hinv : (2 : ℝ) ≤ 1 / p := by
    rw [le_div_iff₀ hp]
    linarith
  have hlog : Real.log 2 ≤ Real.log (1 / p) :=
    Real.log_le_log (by norm_num) hinv
  rw [samplingLogFactor, log₂, le_div_iff₀ (Real.log_pos (by norm_num))]
  simpa using hlog

theorem two_rpow_neg_samplingLogFactor_eq
    {p : ℝ} (hp : 0 < p) :
    Real.rpow 2 (-samplingLogFactor p) = p := by
  have hlogInv : Real.log (1 / p) = -Real.log p := by
    rw [one_div, Real.log_inv]
  calc
    Real.rpow 2 (-samplingLogFactor p) =
        Real.exp (Real.log 2 * (-samplingLogFactor p)) := by
      rw [Real.rpow_eq_pow,
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ = Real.exp (Real.log p) := by
      congr 1
      rw [samplingLogFactor, log₂, hlogInv]
      field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    _ = p := Real.exp_log hp

theorem pow_eq_two_rpow_neg_nat_mul_samplingLogFactor
    {p : ℝ} (hp : 0 < p) (degree : Nat) :
    p ^ degree =
      Real.rpow 2 (-(degree : ℝ) * samplingLogFactor p) := by
  let logFactor := samplingLogFactor p
  have hpTwo : p = Real.rpow 2 (-logFactor) := by
    dsimp [logFactor]
    exact (two_rpow_neg_samplingLogFactor_eq hp).symm
  calc
    p ^ degree = (Real.rpow 2 (-logFactor)) ^ degree := by rw [hpTwo]
    _ = Real.rpow 2 ((-logFactor) * (degree : ℝ)) := by
      rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
      exact (Real.rpow_mul_natCast (by norm_num) _ degree).symm
    _ = Real.rpow 2 (-(degree : ℝ) * samplingLogFactor p) := by
      congr 1
      dsimp [logFactor]
      ring

theorem samplingPeakBaseline_pos
    (updated : ℝ) {p : ℝ} (hp : 0 < p) :
    0 < samplingPeakBaseline updated p := by
  unfold samplingPeakBaseline
  exact div_pos (Real.rpow_pos_of_pos hp _) (by norm_num)

theorem samplingPeakBaseline_le_one
    (updated : ℝ) {p : ℝ} (hupdated : 0 ≤ updated)
    (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    samplingPeakBaseline updated p ≤ 1 := by
  have hpOne : p ≤ 1 := hhalf.trans (by norm_num)
  have hpow : Real.rpow p (4 * updated) ≤ 1 := by
    rw [Real.rpow_eq_pow]
    exact Real.rpow_le_one hp.le hpOne (mul_nonneg (by norm_num) hupdated)
  have hpowPositive : 0 < Real.rpow p (4 * updated) :=
    Real.rpow_pos_of_pos hp _
  unfold samplingPeakBaseline
  nlinarith

theorem one_le_samplingLambda
    (updated : ℝ) {p : ℝ} (hupdated : 0 ≤ updated)
    (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    1 ≤ samplingLambda updated p := by
  have hlog := one_le_samplingLogFactor hp hhalf
  unfold samplingLambda
  have hproduct : 0 ≤ updated * samplingLogFactor p :=
    mul_nonneg hupdated (by linarith)
  linarith

theorem log_four_div_samplingPeakBaseline_le_four_samplingLambda
    (updated : ℝ) {p : ℝ} (hupdated : 0 ≤ updated)
    (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    Real.log (4 / samplingPeakBaseline updated p) ≤
      4 * samplingLambda updated p := by
  let exponent : ℝ := 4 * updated
  let logFactor : ℝ := samplingLogFactor p
  let power : ℝ := Real.rpow p exponent
  have hpPower : 0 < power := by
    dsimp [power]
    exact Real.rpow_pos_of_pos hp _
  have hratio :
      4 / samplingPeakBaseline updated p = 16 / power := by
    dsimp [samplingPeakBaseline, exponent, power]
    field_simp
    ring
  have hlogInv : Real.log (1 / p) = Real.log 2 * logFactor := by
    dsimp [logFactor, samplingLogFactor, log₂]
    field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hlogP : Real.log p = -(Real.log 2 * logFactor) := by
    have hinv := Real.log_inv p
    rw [← one_div] at hinv
    linarith
  have hlogTwoUpper : Real.log 2 ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogPower : Real.log power = exponent * Real.log p := by
    dsimp [power]
    rw [Real.log_rpow hp]
  have hlogSixteen : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : Nat) by norm_num, Real.log_pow]
    norm_num
  have hlambdaNonnegative :
      0 ≤ 1 + updated * logFactor := by
    have hlog := one_le_samplingLogFactor hp hhalf
    have hlogNonnegative : 0 ≤ logFactor := by linarith
    exact add_nonneg zero_le_one
      (mul_nonneg hupdated hlogNonnegative)
  have hexact :
      Real.log (4 / samplingPeakBaseline updated p) =
        4 * Real.log 2 * (1 + updated * logFactor) := by
    calc
      Real.log (4 / samplingPeakBaseline updated p) =
          Real.log (16 / power) := congrArg Real.log hratio
      _ = Real.log 16 - Real.log power :=
        Real.log_div (by norm_num) (ne_of_gt hpPower)
      _ = 4 * Real.log 2 - exponent * Real.log p := by
        rw [hlogSixteen, hlogPower]
      _ = 4 * Real.log 2 * (1 + updated * logFactor) := by
        dsimp [exponent]
        rw [hlogP]
        ring
  rw [hexact]
  dsimp [samplingLambda, logFactor]
  have hscaled :=
    mul_le_mul_of_nonneg_right hlogTwoUpper hlambdaNonnegative
  nlinarith

theorem two_rpow_neg_six_samplingLambda_mul_logFactor_le_baseline
    {updated p : ℝ} (hupdated : 0 ≤ updated)
    (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    Real.rpow 2
        (-6 * samplingLambda updated p * samplingLogFactor p) ≤
      samplingPeakBaseline updated p := by
  let lambda := samplingLambda updated p
  let logFactor := samplingLogFactor p
  let baseline := samplingPeakBaseline updated p
  have hlambda : 1 ≤ lambda := by
    dsimp [lambda]
    exact one_le_samplingLambda updated hupdated hp hhalf
  have hlogFactor : 1 ≤ logFactor := by
    dsimp [logFactor]
    exact one_le_samplingLogFactor hp hhalf
  have hbaseline : 0 < baseline := by
    dsimp [baseline]
    exact samplingPeakBaseline_pos updated hp
  have hpeakHeight : Real.log (4 / baseline) ≤ 4 * lambda := by
    dsimp [baseline, lambda]
    exact log_four_div_samplingPeakBaseline_le_four_samplingLambda
      updated hupdated hp hhalf
  have hconstant : (4 : ℝ) ≤ 6 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hexponentSize :
      4 * lambda ≤ 6 * Real.log 2 * lambda * logFactor := by
    have hlambdaNonnegative : 0 ≤ lambda := by linarith
    have hfirst := mul_le_mul_of_nonneg_right hconstant hlambdaNonnegative
    have hmiddleNonnegative : 0 ≤ 6 * Real.log 2 * lambda := by positivity
    have hsecond := mul_le_mul_of_nonneg_left hlogFactor hmiddleNonnegative
    nlinarith
  have htargetExp :
      Real.rpow 2 (-6 * lambda * logFactor) ≤ Real.exp (-4 * lambda) := by
    rw [Real.rpow_eq_pow,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hratio : 4 / baseline ≤ Real.exp (4 * lambda) := by
    calc
      4 / baseline = Real.exp (Real.log (4 / baseline)) := by
        rw [Real.exp_log]
        positivity
      _ ≤ Real.exp (4 * lambda) := Real.exp_le_exp.mpr hpeakHeight
  have hfour : (4 : ℝ) ≤ Real.exp (4 * lambda) * baseline := by
    calc
      (4 : ℝ) = (4 / baseline) * baseline := by field_simp
      _ ≤ Real.exp (4 * lambda) * baseline :=
        mul_le_mul_of_nonneg_right hratio hbaseline.le
  have hexpBaseline : Real.exp (-4 * lambda) ≤ baseline := by
    rw [show -4 * lambda = -(4 * lambda) by ring,
      Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos (4 * lambda))).2
    nlinarith
  simpa [lambda, logFactor, baseline] using htargetExp.trans hexpBaseline

theorem exists_fiberL1_samplingPeak_uniform
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} {updated p : ℝ}
    (hupdated : 0 ≤ updated) (hp : 0 < p) (hhalf : p ≤ 1 / 2)
    (f : (Fin k → Alphabet) → ℝ) (peak : Fin k → Alphabet)
    (hfL1 : ∑ point, |f point| ≤ 1)
    (hfpeak : samplingPeakBaseline updated p ≤ |f peak|) :
    ∃ coordinates : Finset (Fin k),
      (coordinates.card : ℝ) ≤
          48 * (Real.sqrt ((k : ℝ) * samplingLambda updated p) +
            samplingLambda updated p) ∧
        Real.rpow 2
            (-192 * (Real.sqrt ((k : ℝ) * samplingLambda updated p) +
              samplingLambda updated p) * samplingLogFactor p) ≤
          fiberL1 f coordinates := by
  let lambda := samplingLambda updated p
  let logFactor := samplingLogFactor p
  have hlogFactor : 1 ≤ logFactor := by
    dsimp [logFactor]
    exact one_le_samplingLogFactor hp hhalf
  have hlambda : 1 ≤ lambda := by
    dsimp [lambda]
    exact one_le_samplingLambda updated hupdated hp hhalf
  have hbaselinePositive := samplingPeakBaseline_pos updated hp
  have hbaselineOne := samplingPeakBaseline_le_one updated hupdated hp hhalf
  have hpeakHeight :=
    log_four_div_samplingPeakBaseline_le_four_samplingLambda
      updated hupdated hp hhalf
  obtain ⟨coordinates, hcard, hfiber⟩ :=
    exists_fiberL1_larsenCutoff_uniform
      hbaselinePositive hbaselineOne (height := 4 * lambda)
      (logFactor := (1 : ℝ)) (by linarith) (by norm_num)
      (by simpa [lambda] using hpeakHeight) f peak hfL1 hfpeak
  have hlambdaNonnegative : 0 ≤ lambda := by linarith
  have hroot :
      Real.sqrt ((k : ℝ) * (4 * lambda)) =
        2 * Real.sqrt ((k : ℝ) * lambda) := by
    rw [show (k : ℝ) * (4 * lambda) =
        4 * ((k : ℝ) * lambda) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hcardFinal : (coordinates.card : ℝ) ≤
      48 * (Real.sqrt ((k : ℝ) * lambda) + lambda) := by
    rw [hroot] at hcard
    simp only [mul_one] at hcard
    have hsqrt := Real.sqrt_nonneg ((k : ℝ) * lambda)
    nlinarith
  have htarget :
      Real.rpow 2
          (-192 * (Real.sqrt ((k : ℝ) * lambda) + lambda) * logFactor) ≤
        larsenFiberReward k (4 * lambda) 1 := by
    rw [larsenFiberReward, Real.rpow_eq_pow, Real.rpow_eq_pow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [hroot]
    have hsqrt : 0 ≤ Real.sqrt ((k : ℝ) * lambda) := Real.sqrt_nonneg _
    have hshape : 0 ≤ Real.sqrt ((k : ℝ) * lambda) + lambda := by linarith
    have hscaled := mul_le_mul_of_nonneg_left hlogFactor hshape
    nlinarith
  refine ⟨coordinates, ?_, ?_⟩
  · simpa [lambda] using hcardFinal
  · simpa [lambda, logFactor] using htarget.trans hfiber

theorem exists_fiberL1_samplingPeak_of_dimension_le_four_total
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} {updated p total : ℝ}
    (hupdated : 0 ≤ updated) (hp : 0 < p) (hhalf : p ≤ 1 / 2)
    (htotal : 0 ≤ total) (hdimension : (k : ℝ) ≤ 4 * total)
    (f : (Fin k → Alphabet) → ℝ) (peak : Fin k → Alphabet)
    (hfL1 : ∑ point, |f point| ≤ 1)
    (hfpeak : samplingPeakBaseline updated p ≤ |f peak|) :
    ∃ coordinates : Finset (Fin k),
      (coordinates.card : ℝ) ≤
          96 * (Real.sqrt (total * samplingLambda updated p) +
            samplingLambda updated p) ∧
        Real.rpow 2
            (-384 * (Real.sqrt (total * samplingLambda updated p) +
              samplingLambda updated p) * samplingLogFactor p) ≤
          fiberL1 f coordinates := by
  let lambda := samplingLambda updated p
  let logFactor := samplingLogFactor p
  have hlambda : 1 ≤ lambda := by
    dsimp [lambda]
    exact one_le_samplingLambda updated hupdated hp hhalf
  have hlogFactor : 1 ≤ logFactor := by
    dsimp [logFactor]
    exact one_le_samplingLogFactor hp hhalf
  have hlambdaNonnegative : 0 ≤ lambda := by linarith
  have hlogFactorNonnegative : 0 ≤ logFactor := by linarith
  have htotalLambdaNonnegative : 0 ≤ total * lambda :=
    mul_nonneg htotal hlambdaNonnegative
  obtain ⟨coordinates, hcard, hfiber⟩ :=
    exists_fiberL1_samplingPeak_uniform hupdated hp hhalf f peak hfL1 hfpeak
  have hroot :
      Real.sqrt ((k : ℝ) * lambda) ≤
        2 * Real.sqrt (total * lambda) := by
    calc
      Real.sqrt ((k : ℝ) * lambda) ≤
          Real.sqrt ((4 * total) * lambda) := by
        apply Real.sqrt_le_sqrt
        exact mul_le_mul_of_nonneg_right hdimension hlambdaNonnegative
      _ = Real.sqrt (4 * (total * lambda)) := by
        congr 1
        ring
      _ = 2 * Real.sqrt (total * lambda) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
  have hcardFinal : (coordinates.card : ℝ) ≤
      96 * (Real.sqrt (total * lambda) + lambda) := by
    have hsqrt : 0 ≤ Real.sqrt (total * lambda) := Real.sqrt_nonneg _
    nlinarith [htotalLambdaNonnegative]
  have htarget :
      Real.rpow 2
          (-384 * (Real.sqrt (total * lambda) + lambda) * logFactor) ≤
        Real.rpow 2
          (-192 * (Real.sqrt ((k : ℝ) * lambda) + lambda) * logFactor) := by
    rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hsqrt : 0 ≤ Real.sqrt (total * lambda) := Real.sqrt_nonneg _
    have hshape :
        Real.sqrt ((k : ℝ) * lambda) + lambda ≤
          2 * (Real.sqrt (total * lambda) + lambda) := by
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_right hshape hlogFactorNonnegative
    nlinarith
  refine ⟨coordinates, ?_, ?_⟩
  · simpa [lambda] using hcardFinal
  · simpa [lambda, logFactor] using htarget.trans hfiber


def samplingShape (total updated p : ℝ) : ℝ :=
  Real.sqrt (total * samplingLambda updated p) + samplingLambda updated p

def samplingRevealBudget (total updated p : ℝ) : Nat :=
  ⌈96 * samplingShape total updated p⌉₊

theorem two_rpow_neg_512_samplingShape_le_reveal_mul_peak_mul_fiberReward
    {total updated p : ℝ}
    (htotal : 0 ≤ total) (hupdated : 0 ≤ updated)
    (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    Real.rpow 2
        (-512 * samplingShape total updated p * samplingLogFactor p) ≤
      p ^ samplingRevealBudget total updated p *
        (samplingPeakBaseline updated p *
          Real.rpow 2
            (-384 * samplingShape total updated p * samplingLogFactor p)) := by
  let lambda := samplingLambda updated p
  let logFactor := samplingLogFactor p
  let shape := samplingShape total updated p
  let degree := samplingRevealBudget total updated p
  have hlambda : 1 ≤ lambda := by
    dsimp [lambda]
    exact one_le_samplingLambda updated hupdated hp hhalf
  have hlogFactor : 1 ≤ logFactor := by
    dsimp [logFactor]
    exact one_le_samplingLogFactor hp hhalf
  have hlambdaNonnegative : 0 ≤ lambda := by linarith
  have hlogFactorNonnegative : 0 ≤ logFactor := by linarith
  have hshape : 1 ≤ shape := by
    dsimp [shape, samplingShape, lambda]
    have hproduct : 0 ≤ total * samplingLambda updated p :=
      mul_nonneg htotal (by
        linarith [one_le_samplingLambda updated hupdated hp hhalf])
    have hsqrt : 0 ≤ Real.sqrt
        (total * samplingLambda updated p) := by
      have hsqrtMono :
          Real.sqrt 0 ≤ Real.sqrt
            (total * samplingLambda updated p) :=
        Real.sqrt_le_sqrt hproduct
      rw [Real.sqrt_zero] at hsqrtMono
      exact hsqrtMono
    linarith
  have hshapeNonnegative : 0 ≤ shape := by linarith
  have hdegree : (degree : ℝ) ≤ 97 * shape := by
    have hceil :=
      (Nat.ceil_lt_add_one (a := (96 : ℝ) * shape)
        (mul_nonneg (by norm_num) hshapeNonnegative)).le
    dsimp [degree, samplingRevealBudget]
    linarith
  have hpLower :
      Real.rpow 2 (-97 * shape * logFactor) ≤ p ^ degree := by
    have hexponent :
        -97 * shape * logFactor ≤ -(degree : ℝ) * logFactor := by
      have hscaled := mul_le_mul_of_nonneg_right hdegree hlogFactorNonnegative
      nlinarith
    calc
      Real.rpow 2 (-97 * shape * logFactor) ≤
          Real.rpow 2 (-(degree : ℝ) * logFactor) := by
        rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
      _ = p ^ degree := by
        dsimp [logFactor]
        exact (pow_eq_two_rpow_neg_nat_mul_samplingLogFactor hp degree).symm
  have hbaselineRaw :=
    two_rpow_neg_six_samplingLambda_mul_logFactor_le_baseline
      hupdated hp hhalf
  have hbaselineLower :
      Real.rpow 2 (-6 * shape * logFactor) ≤
        samplingPeakBaseline updated p := by
    have hlambdaShape : lambda ≤ shape := by
      dsimp [shape, samplingShape, lambda]
      exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
    have hexponent :
        -6 * shape * logFactor ≤ -6 * lambda * logFactor := by
      have hscaled :=
        mul_le_mul_of_nonneg_right hlambdaShape hlogFactorNonnegative
      nlinarith
    calc
      Real.rpow 2 (-6 * shape * logFactor) ≤
          Real.rpow 2 (-6 * lambda * logFactor) := by
        rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
      _ ≤ samplingPeakBaseline updated p := by
        simpa [lambda, logFactor] using hbaselineRaw
  have hconstant :
      Real.rpow 2 (-512 * shape * logFactor) ≤
        Real.rpow 2 (-487 * shape * logFactor) := by
    rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [mul_nonneg hshapeNonnegative hlogFactorNonnegative]
  have hsplit :
      Real.rpow 2 (-487 * shape * logFactor) =
        Real.rpow 2 (-97 * shape * logFactor) *
          (Real.rpow 2 (-6 * shape * logFactor) *
            Real.rpow 2 (-384 * shape * logFactor)) := by
    rw [Real.rpow_eq_pow, Real.rpow_eq_pow, Real.rpow_eq_pow,
      Real.rpow_eq_pow]
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hfiberNonnegative :
      0 ≤ Real.rpow 2 (-384 * shape * logFactor) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    Real.rpow 2
        (-512 * samplingShape total updated p * samplingLogFactor p) =
        Real.rpow 2 (-512 * shape * logFactor) := by rfl
    _ ≤ Real.rpow 2 (-487 * shape * logFactor) := hconstant
    _ = Real.rpow 2 (-97 * shape * logFactor) *
        (Real.rpow 2 (-6 * shape * logFactor) *
          Real.rpow 2 (-384 * shape * logFactor)) := hsplit
    _ ≤ p ^ degree *
        (samplingPeakBaseline updated p *
          Real.rpow 2 (-384 * shape * logFactor)) := by
      apply mul_le_mul hpLower
      · exact mul_le_mul_of_nonneg_right hbaselineLower hfiberNonnegative
      · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hfiberNonnegative
      · exact pow_nonneg hp.le degree
    _ = p ^ samplingRevealBudget total updated p *
        (samplingPeakBaseline updated p *
          Real.rpow 2
            (-384 * samplingShape total updated p * samplingLogFactor p)) := by
      rfl

end

end PegSeparation.External.LarsenYuPeakQuantitative
