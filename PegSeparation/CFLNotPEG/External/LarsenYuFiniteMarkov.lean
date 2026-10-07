import PegSeparation.CFLNotPEG.External.LarsenYuBernoulliEvents


open scoped BigOperators

namespace PegSeparation.External.LarsenYuFiniteMarkov

noncomputable section

open LarsenYuBernoulliEvents

def expectation {Outcome : Type} [Fintype Outcome]
    (distribution : FiniteDistribution Outcome) (cost : Outcome → ℝ) : ℝ :=
  ∑ outcome : Outcome, distribution.mass outcome * cost outcome

theorem expectation_nonneg
    {Outcome : Type} [Fintype Outcome]
    (distribution : FiniteDistribution Outcome) (cost : Outcome → ℝ)
    (hcost : ∀ outcome, 0 ≤ cost outcome) :
    0 ≤ expectation distribution cost := by
  unfold expectation
  apply Finset.sum_nonneg
  intro outcome _houtcome
  exact mul_nonneg (distribution.mass_nonnegative outcome) (hcost outcome)

theorem eventMass_cost_gt_four_expectation_le
    {Outcome : Type} [Fintype Outcome]
    (distribution : FiniteDistribution Outcome) (cost : Outcome → ℝ)
    (hcost : ∀ outcome, 0 ≤ cost outcome) :
    eventMass distribution
        (fun outcome ↦ 4 * expectation distribution cost < cost outcome) ≤
      (1 / 4 : ℝ) := by
  classical
  let expected : ℝ := expectation distribution cost
  have hexpected : 0 ≤ expected := expectation_nonneg distribution cost hcost
  by_cases hzero : expected = 0
  · have hterm (outcome : Outcome) :
        distribution.mass outcome * cost outcome = 0 := by
      have hsum :
          (∑ outcome : Outcome, distribution.mass outcome * cost outcome) = 0 := by
        simpa [expected, expectation] using hzero
      have hall : (fun outcome : Outcome ↦
          distribution.mass outcome * cost outcome) = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg
          (fun outcome ↦ mul_nonneg (distribution.mass_nonnegative outcome)
            (hcost outcome))).mp hsum
      exact congrFun hall outcome
    have hevent : eventMass distribution
        (fun outcome ↦ 4 * expectation distribution cost < cost outcome) = 0 := by
      unfold eventMass
      apply Finset.sum_eq_zero
      intro outcome _houtcome
      by_cases hbad : 4 * expectation distribution cost < cost outcome
      · have hcostPositive : 0 < cost outcome := by
          simpa [expected, hzero] using hbad
        have hmass : distribution.mass outcome = 0 :=
          (mul_eq_zero.mp (hterm outcome)).resolve_right hcostPositive.ne'
        simp [hbad, hmass]
      · simp [hbad]
    rw [hevent]
    norm_num
  · have hexpectedPositive : 0 < expected := lt_of_le_of_ne hexpected (Ne.symm hzero)
    have hpoint (outcome : Outcome) :
        distribution.mass outcome *
            (if 4 * expected < cost outcome then 1 else 0) ≤
          (distribution.mass outcome * cost outcome) / (4 * expected) := by
      by_cases hbad : 4 * expected < cost outcome
      · simp only [hbad, if_true, mul_one]
        apply (le_div_iff₀ (by positivity)).2
        nlinarith [distribution.mass_nonnegative outcome]
      · simp only [hbad, if_false, mul_zero]
        exact div_nonneg
          (mul_nonneg (distribution.mass_nonnegative outcome) (hcost outcome))
          (by positivity)
    calc
      eventMass distribution
          (fun outcome ↦ 4 * expectation distribution cost < cost outcome) =
          ∑ outcome : Outcome, distribution.mass outcome *
            (if 4 * expected < cost outcome then 1 else 0) := by
        rfl
      _ ≤ ∑ outcome : Outcome,
          (distribution.mass outcome * cost outcome) / (4 * expected) := by
        exact Finset.sum_le_sum fun outcome _houtcome ↦ hpoint outcome
      _ = expected / (4 * expected) := by
        rw [← Finset.sum_div]
        rfl
      _ = 1 / 4 := by
        field_simp

theorem eventMass_or_le_add
    {Outcome : Type} [Fintype Outcome]
    (distribution : FiniteDistribution Outcome)
    (left right : Outcome → Prop) [DecidablePred left] [DecidablePred right] :
    eventMass distribution (fun outcome ↦ left outcome ∨ right outcome) ≤
      eventMass distribution left + eventMass distribution right := by
  classical
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro outcome _houtcome
  by_cases hleft : left outcome <;> by_cases hright : right outcome <;>
    simp [hleft, hright, distribution.mass_nonnegative outcome]

theorem eventMass_two_bad_le_half
    {Outcome : Type} [Fintype Outcome]
    (distribution : FiniteDistribution Outcome)
    (firstCost secondCost : Outcome → ℝ)
    (hfirst : ∀ outcome, 0 ≤ firstCost outcome)
    (hsecond : ∀ outcome, 0 ≤ secondCost outcome) :
    eventMass distribution (fun outcome ↦
        4 * expectation distribution firstCost < firstCost outcome ∨
        4 * expectation distribution secondCost < secondCost outcome) ≤
      (1 / 2 : ℝ) := by
  calc
    _ ≤ eventMass distribution (fun outcome ↦
          4 * expectation distribution firstCost < firstCost outcome) +
        eventMass distribution (fun outcome ↦
          4 * expectation distribution secondCost < secondCost outcome) :=
      eventMass_or_le_add distribution _ _
    _ ≤ 1 / 4 + 1 / 4 := add_le_add
      (eventMass_cost_gt_four_expectation_le distribution firstCost hfirst)
      (eventMass_cost_gt_four_expectation_le distribution secondCost hsecond)
    _ = 1 / 2 := by norm_num

end

end PegSeparation.External.LarsenYuFiniteMarkov
