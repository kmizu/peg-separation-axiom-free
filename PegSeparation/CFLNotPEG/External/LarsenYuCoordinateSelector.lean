import PegSeparation.CFLNotPEG.External.LarsenYuAdaptiveSampling


open scoped BigOperators

namespace PegSeparation.External.LarsenYuCoordinateSelector

noncomputable section

theorem exists_dependentSelector
    {View : Type}
    (dimension : View → Nat)
    (eligible : View → Prop)
    (budget lower : ℝ)
    (reward : (view : View) → Finset (Fin (dimension view)) → ℝ)
    (hexists : ∀ view, eligible view →
      ∃ coordinates : Finset (Fin (dimension view)),
        (coordinates.card : ℝ) ≤ budget ∧
          lower ≤ reward view coordinates) :
    ∃ selector : (view : View) → Finset (Fin (dimension view)),
      (∀ view, (selector view).card ≤ ⌈budget⌉₊) ∧
        ∀ view, eligible view → lower ≤ reward view (selector view) := by
  classical
  let selector : (view : View) → Finset (Fin (dimension view)) :=
    fun view ↦ if h : eligible view then (hexists view h).choose else ∅
  refine ⟨selector, ?_, ?_⟩
  · intro view
    by_cases heligible : eligible view
    · have hcard : ((selector view).card : ℝ) ≤ budget := by
        simpa [selector, heligible] using (hexists view heligible).choose_spec.1
      have hceil : (budget : ℝ) ≤ (⌈budget⌉₊ : Nat) := Nat.le_ceil budget
      have : ((selector view).card : ℝ) ≤ (⌈budget⌉₊ : Nat) :=
        hcard.trans hceil
      exact_mod_cast this
    · simp [selector, heligible]
  · intro view heligible
    simpa [selector, heligible] using (hexists view heligible).choose_spec.2

theorem lower_mul_eligibleMass_le_selectedReward
    {View : Type} [Fintype View]
    (dimension : View → Nat)
    (eligible : View → Prop) [DecidablePred eligible]
    (mass : View → ℝ) (hmass : ∀ view, 0 ≤ mass view)
    (lower : ℝ)
    (reward : (view : View) → Finset (Fin (dimension view)) → ℝ)
    (selector : (view : View) → Finset (Fin (dimension view)))
    (hselector : ∀ view, eligible view →
      lower ≤ reward view (selector view)) :
    lower * (∑ view, if eligible view then mass view else 0) ≤
      ∑ view, if eligible view then
        mass view * reward view (selector view) else 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro view _hview
  by_cases heligible : eligible view
  · simp only [heligible, if_true]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hselector view heligible) (hmass view)
  · simp [heligible]

end

end PegSeparation.External.LarsenYuCoordinateSelector
