import PegSeparation.CFLNotPEG.External.PeakToAverage


open scoped BigOperators

namespace PegSeparation.External.LarsenYuPosteriorFiltering

noncomputable section

theorem half_baseline_le_goodFiberMass
    {Fiber : Type} [Fintype Fiber]
    (mass success : Fiber → ℝ) (baseline : ℝ)
    (hbaseline : 0 ≤ baseline)
    (hmass_nonnegative : ∀ fiber, 0 ≤ mass fiber)
    (hmass_sum : ∑ fiber, mass fiber = 1)
    (hsuccess_le_mass : ∀ fiber, success fiber ≤ mass fiber)
    (hglobal : baseline ≤ ∑ fiber, success fiber) :
    baseline / 2 ≤
      ∑ fiber, if baseline / 2 * mass fiber ≤ success fiber
        then mass fiber else 0 := by
  classical
  let good : Fiber → Prop :=
    fun fiber ↦ baseline / 2 * mass fiber ≤ success fiber
  have hpointwise (fiber : Fiber) :
      success fiber ≤
        if good fiber then mass fiber else baseline / 2 * mass fiber := by
    by_cases hgood : good fiber
    · simpa [hgood] using hsuccess_le_mass fiber
    · simp only [hgood, if_false]
      exact (lt_of_not_ge hgood).le
  have hbadMass :
      (∑ fiber, if good fiber then 0 else mass fiber) ≤ 1 := by
    calc
      (∑ fiber, if good fiber then 0 else mass fiber) ≤
          ∑ fiber, mass fiber := by
        apply Finset.sum_le_sum
        intro fiber _
        by_cases hgood : good fiber
        · simp [hgood, hmass_nonnegative fiber]
        · simp [hgood]
      _ = 1 := hmass_sum
  have hdecompose :
      (∑ fiber, if good fiber then mass fiber
        else baseline / 2 * mass fiber) =
      (∑ fiber, if good fiber then mass fiber else 0) +
        baseline / 2 * (∑ fiber, if good fiber then 0 else mass fiber) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro fiber _
    by_cases hgood : good fiber <;> simp [hgood]
  have hupper :
      (∑ fiber, if good fiber then mass fiber
        else baseline / 2 * mass fiber) ≤
      (∑ fiber, if good fiber then mass fiber else 0) + baseline / 2 := by
    rw [hdecompose]
    have hhalf : 0 ≤ baseline / 2 := by positivity
    have hmul : baseline / 2 *
        (∑ fiber, if good fiber then 0 else mass fiber) ≤
        baseline / 2 * 1 :=
      mul_le_mul_of_nonneg_left hbadMass hhalf
    nlinarith [hmul]
  have hchain :
      baseline ≤ (∑ fiber, if good fiber then mass fiber else 0) +
        baseline / 2 :=
    hglobal.trans ((Finset.sum_le_sum fun fiber _ ↦ hpointwise fiber).trans hupper)
  change baseline / 2 ≤ ∑ fiber, if good fiber then mass fiber else 0
  linarith


def coarseMass
    {Input View : Type} [Fintype Input] [Fintype View] [DecidableEq View]
    (distribution : FiniteDistribution Input) (view : Input → View)
    (selectedView : View) : ℝ :=
  ∑ input, distribution.mass input *
    if view input = selectedView then 1 else 0

def successMass
    {Input View : Type} [Fintype Input] [Fintype View] [DecidableEq View]
    (distribution : FiniteDistribution Input) (view : Input → View)
    (success : Input → Prop) [DecidablePred success]
    (selectedView : View) : ℝ :=
  ∑ input, distribution.mass input *
    if view input = selectedView ∧ success input then 1 else 0

def contentMass
    {Input View Content : Type}
    [Fintype Input] [Fintype View] [Fintype Content]
    [DecidableEq View] [DecidableEq Content]
    (distribution : FiniteDistribution Input)
    (view : Input → View) (content : Input → Content)
    (selectedView : View) (selectedContent : Content) : ℝ :=
  ∑ input, distribution.mass input *
    if view input = selectedView ∧ content input = selectedContent then 1 else 0

def signedContentMass
    {Input View Content : Type}
    [Fintype Input] [Fintype View] [Fintype Content]
    [DecidableEq View] [DecidableEq Content]
    (distribution : FiniteDistribution Input)
    (view : Input → View) (content : Input → Content)
    (signal : Input → ℝ)
    (selectedView : View) (selectedContent : Content) : ℝ :=
  ∑ input, distribution.mass input *
    if view input = selectedView ∧ content input = selectedContent
      then signal input else 0

def normalizedSignedContent
    {Input View Content : Type}
    [Fintype Input] [Fintype View] [Fintype Content]
    [DecidableEq View] [DecidableEq Content]
    (distribution : FiniteDistribution Input)
    (view : Input → View) (content : Input → Content)
    (signal : Input → ℝ) (selectedView : View) :
    Content → ℝ :=
  fun selectedContent ↦
    signedContentMass distribution view content signal selectedView selectedContent /
      coarseMass distribution view selectedView

theorem coarseMass_nonnegative
    {Input View : Type} [Fintype Input] [Fintype View] [DecidableEq View]
    (distribution : FiniteDistribution Input) (view : Input → View)
    (selectedView : View) :
    0 ≤ coarseMass distribution view selectedView := by
  unfold coarseMass
  apply Finset.sum_nonneg
  intro input _
  split <;> simp [distribution.mass_nonnegative input]

theorem sum_coarseMass
    {Input View : Type} [Fintype Input] [Fintype View] [DecidableEq View]
    (distribution : FiniteDistribution Input) (view : Input → View) :
    ∑ selectedView, coarseMass distribution view selectedView = 1 := by
  classical
  unfold coarseMass
  rw [Finset.sum_comm]
  calc
    (∑ input, ∑ selectedView,
      distribution.mass input *
        if view input = selectedView then 1 else 0) =
        ∑ input, distribution.mass input := by
      apply Finset.sum_congr rfl
      intro input _
      rw [Fintype.sum_eq_single (view input)]
      · simp
      · intro other hne
        simp [hne.symm]
    _ = 1 := distribution.mass_sum

theorem successMass_nonnegative
    {Input View : Type} [Fintype Input] [Fintype View] [DecidableEq View]
    (distribution : FiniteDistribution Input) (view : Input → View)
    (success : Input → Prop) [DecidablePred success]
    (selectedView : View) :
    0 ≤ successMass distribution view success selectedView := by
  unfold successMass
  apply Finset.sum_nonneg
  intro input _
  split <;> simp [distribution.mass_nonnegative input]

theorem successMass_le_coarseMass
    {Input View : Type} [Fintype Input] [Fintype View] [DecidableEq View]
    (distribution : FiniteDistribution Input) (view : Input → View)
    (success : Input → Prop) [DecidablePred success]
    (selectedView : View) :
    successMass distribution view success selectedView ≤
      coarseMass distribution view selectedView := by
  unfold successMass coarseMass
  apply Finset.sum_le_sum
  intro input _
  by_cases hview : view input = selectedView
  · by_cases hsuccess : success input <;>
      simp [hview, hsuccess, distribution.mass_nonnegative input]
  · simp [hview]

theorem sum_successMass
    {Input View : Type} [Fintype Input] [Fintype View] [DecidableEq View]
    (distribution : FiniteDistribution Input) (view : Input → View)
    (success : Input → Prop) [DecidablePred success] :
    (∑ selectedView, successMass distribution view success selectedView) =
      ∑ input, distribution.mass input * if success input then 1 else 0 := by
  classical
  unfold successMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  by_cases hsuccess : success input
  · rw [Fintype.sum_eq_single (view input)]
    · simp [hsuccess]
    · intro other hne
      simp [hsuccess, hne.symm]
  · simp [hsuccess]

theorem contentMass_nonnegative
    {Input View Content : Type}
    [Fintype Input] [Fintype View] [Fintype Content]
    [DecidableEq View] [DecidableEq Content]
    (distribution : FiniteDistribution Input)
    (view : Input → View) (content : Input → Content)
    (selectedView : View) (selectedContent : Content) :
    0 ≤ contentMass distribution view content selectedView selectedContent := by
  unfold contentMass
  apply Finset.sum_nonneg
  intro input _
  split <;> simp [distribution.mass_nonnegative input]

theorem sum_contentMass
    {Input View Content : Type}
    [Fintype Input] [Fintype View] [Fintype Content]
    [DecidableEq View] [DecidableEq Content]
    (distribution : FiniteDistribution Input)
    (view : Input → View) (content : Input → Content)
    (selectedView : View) :
    ∑ selectedContent,
      contentMass distribution view content selectedView selectedContent =
        coarseMass distribution view selectedView := by
  classical
  unfold contentMass coarseMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  by_cases hview : view input = selectedView
  · rw [Fintype.sum_eq_single (content input)]
    · simp [hview]
    · intro other hne
      simp [hview, hne.symm]
  · simp [hview]

theorem sum_abs_signedContentMass_le_coarseMass
    {Input View Content : Type}
    [Fintype Input] [Fintype View] [Fintype Content]
    [DecidableEq View] [DecidableEq Content]
    (distribution : FiniteDistribution Input)
    (view : Input → View) (content : Input → Content)
    (signal : Input → ℝ) (selectedView : View)
    (hsignal : ∀ input, |signal input| ≤ 1) :
    (∑ selectedContent,
      |signedContentMass distribution view content signal
        selectedView selectedContent|) ≤
      coarseMass distribution view selectedView := by
  classical
  calc
    (∑ selectedContent,
      |signedContentMass distribution view content signal
        selectedView selectedContent|) ≤
      ∑ selectedContent, ∑ input,
        |distribution.mass input *
          (if view input = selectedView ∧ content input = selectedContent
            then signal input else 0)| := by
      apply Finset.sum_le_sum
      intro selectedContent _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ selectedContent, ∑ input,
        distribution.mass input *
          (if view input = selectedView ∧ content input = selectedContent
            then 1 else 0) := by
      apply Finset.sum_le_sum
      intro selectedContent _
      apply Finset.sum_le_sum
      intro input _
      by_cases hfiber :
          view input = selectedView ∧ content input = selectedContent
      · simp only [hfiber, abs_mul, abs_of_nonneg
          (distribution.mass_nonnegative input)]
        exact mul_le_mul_of_nonneg_left (hsignal input)
          (distribution.mass_nonnegative input)
      · simp [hfiber]
    _ = coarseMass distribution view selectedView := by
      rw [Finset.sum_comm]
      unfold coarseMass
      apply Finset.sum_congr rfl
      intro input _
      by_cases hview : view input = selectedView
      · rw [Fintype.sum_eq_single (content input)]
        · simp [hview]
        · intro other hne
          simp [hview, hne.symm]
      · simp [hview]

theorem successMass_le_contentMass_of_peak
    {Input View Content : Type}
    [Fintype Input] [Fintype View] [Fintype Content]
    [DecidableEq View] [DecidableEq Content]
    (distribution : FiniteDistribution Input)
    (view : Input → View) (content : Input → Content)
    (success : Input → Prop) [DecidablePred success]
    (selectedView : View) (peak : Content)
    (hsuccessPeak : ∀ input, view input = selectedView →
      success input → content input = peak) :
    successMass distribution view success selectedView ≤
      contentMass distribution view content selectedView peak := by
  unfold successMass contentMass
  apply Finset.sum_le_sum
  intro input _
  by_cases hview : view input = selectedView
  · by_cases hsuccess : success input
    · have hcontent := hsuccessPeak input hview hsuccess
      simp [hview, hsuccess, hcontent]
    · by_cases hcontent : content input = peak <;>
        simp [hview, hsuccess, hcontent, distribution.mass_nonnegative input]
  · simp [hview]

theorem abs_signedContentMass_eq_contentMass_of_fixed
    {Input View Content : Type}
    [Fintype Input] [Fintype View] [Fintype Content]
    [DecidableEq View] [DecidableEq Content]
    (distribution : FiniteDistribution Input)
    (view : Input → View) (content : Input → Content)
    (signal : Input → ℝ) (selectedView : View) (peak : Content)
    (fixedSignal : ℝ) (hfixedAbs : |fixedSignal| = 1)
    (hfixed : ∀ input, view input = selectedView → content input = peak →
      signal input = fixedSignal) :
    |signedContentMass distribution view content signal selectedView peak| =
      contentMass distribution view content selectedView peak := by
  have hsigned :
      signedContentMass distribution view content signal selectedView peak =
        fixedSignal * contentMass distribution view content selectedView peak := by
    unfold signedContentMass contentMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro input _
    by_cases hview : view input = selectedView
    · by_cases hcontent : content input = peak
      · rw [hfixed input hview hcontent]
        simp [hview, hcontent]
        ring
      · simp [hview, hcontent]
    · simp [hview]
  rw [hsigned, abs_mul, hfixedAbs, one_mul,
    abs_of_nonneg (contentMass_nonnegative distribution view content
      selectedView peak)]

theorem sum_abs_normalizedSignedContent_le_one
    {Input View Content : Type}
    [Fintype Input] [Fintype View] [Fintype Content]
    [DecidableEq View] [DecidableEq Content]
    (distribution : FiniteDistribution Input)
    (view : Input → View) (content : Input → Content)
    (signal : Input → ℝ) (selectedView : View)
    (hviewPositive : 0 < coarseMass distribution view selectedView)
    (hsignal : ∀ input, |signal input| ≤ 1) :
    (∑ selectedContent,
      |normalizedSignedContent distribution view content signal
        selectedView selectedContent|) ≤ 1 := by
  unfold normalizedSignedContent
  simp_rw [abs_div, abs_of_pos hviewPositive]
  rw [← Finset.sum_div]
  apply (div_le_iff₀ hviewPositive).2
  simpa using sum_abs_signedContentMass_le_coarseMass
    distribution view content signal selectedView hsignal

theorem baseline_le_abs_normalizedSignedContent_peak
    {Input View Content : Type}
    [Fintype Input] [Fintype View] [Fintype Content]
    [DecidableEq View] [DecidableEq Content]
    (distribution : FiniteDistribution Input)
    (view : Input → View) (content : Input → Content)
    (signal : Input → ℝ)
    (success : Input → Prop) [DecidablePred success]
    (selectedView : View) (peak : Content) (baseline : ℝ)
    (hviewPositive : 0 < coarseMass distribution view selectedView)
    (hgood : baseline * coarseMass distribution view selectedView ≤
      successMass distribution view success selectedView)
    (hsuccessPeak : ∀ input, view input = selectedView →
      success input → content input = peak)
    (fixedSignal : ℝ) (hfixedAbs : |fixedSignal| = 1)
    (hfixed : ∀ input, view input = selectedView → content input = peak →
      signal input = fixedSignal) :
    baseline ≤
      |normalizedSignedContent distribution view content signal
        selectedView peak| := by
  rw [normalizedSignedContent, abs_div, abs_of_pos hviewPositive]
  apply (le_div_iff₀ hviewPositive).2
  calc
    baseline * coarseMass distribution view selectedView ≤
        successMass distribution view success selectedView := hgood
    _ ≤ contentMass distribution view content selectedView peak :=
      successMass_le_contentMass_of_peak distribution view content success
        selectedView peak hsuccessPeak
    _ = |signedContentMass distribution view content signal
        selectedView peak| := by
      symm
      exact abs_signedContentMass_eq_contentMass_of_fixed
        distribution view content signal selectedView peak fixedSignal
          hfixedAbs hfixed

theorem exists_large_posteriorFiberL1_of_goodView
    {Input View Alphabet : Type}
    [Fintype Input] [Fintype View] [Fintype Alphabet]
    [DecidableEq View] [DecidableEq Alphabet]
    {k degree : Nat} {M baseline : ℝ}
    (certificate : PeakToAverage.AndCertificate k degree M)
    (distribution : FiniteDistribution Input)
    (view : Input → View)
    (content : Input → (Fin k → Alphabet))
    (signal : Input → ℝ)
    (success : Input → Prop) [DecidablePred success]
    (selectedView : View) (peak : Fin k → Alphabet)
    (hviewPositive : 0 < coarseMass distribution view selectedView)
    (hbaselinePositive : 0 < baseline)
    (hsignal : ∀ input, |signal input| ≤ 1)
    (hgood : baseline * coarseMass distribution view selectedView ≤
      successMass distribution view success selectedView)
    (hsuccessPeak : ∀ input, view input = selectedView →
      success input → content input = peak)
    (fixedSignal : ℝ) (hfixedAbs : |fixedSignal| = 1)
    (hfixed : ∀ input, view input = selectedView → content input = peak →
      signal input = fixedSignal)
    (hscale : 2 ≤ M * baseline) :
    ∃ coordinates : Finset (Fin k),
      coordinates.card ≤ degree ∧
        1 ≤ certificate.coefficientL1 *
          PeakToAverage.fiberL1
            (normalizedSignedContent distribution view content signal selectedView)
            coordinates := by
  exact PeakToAverage.exists_large_fiberL1_of_certificate
    certificate
    (normalizedSignedContent distribution view content signal selectedView)
    peak hbaselinePositive
    (sum_abs_normalizedSignedContent_le_one
      distribution view content signal selectedView hviewPositive hsignal)
    (baseline_le_abs_normalizedSignedContent_peak
      distribution view content signal success selectedView peak baseline
      hviewPositive hgood hsuccessPeak fixedSignal hfixedAbs hfixed)
    hscale

end

end PegSeparation.External.LarsenYuPosteriorFiltering
