import PegSeparation.CFLNotPEG.External.LarsenYuBernoulliEvents


open scoped BigOperators

namespace PegSeparation.External.LarsenYuAdaptiveSampling

noncomputable section

open LarsenYuBernoulli LarsenYuBernoulliEvents

local instance includesDecidable
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (mask : Mask Coordinate) (required : Finset Coordinate) :
    Decidable (Includes mask required) :=
  LarsenYuBernoulliEvents.includesDecidable mask required

theorem pow_degree_mul_sum_le_maskAverage
    {Coordinate Context : Type}
    [Fintype Coordinate] [DecidableEq Coordinate] [Fintype Context]
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (degree : Nat) (required : Context → Finset Coordinate)
    (hdegree : ∀ context, (required context).card ≤ degree)
    (value : Context → ℝ) (hvalue : ∀ context, 0 ≤ value context) :
    p ^ degree * ∑ context, value context ≤
      ∑ mask : Mask Coordinate,
        (maskDistribution Coordinate p hp hpone).mass mask *
          ∑ context,
            if Includes mask (required context) then value context else 0 := by
  calc
    p ^ degree * ∑ context, value context =
        ∑ context, value context * p ^ degree := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro context _
      ring
    _ ≤ ∑ context, value context * p ^ (required context).card := by
      apply Finset.sum_le_sum
      intro context _
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hp hpone (hdegree context)) (hvalue context)
    _ = ∑ context, value context *
        eventMass (maskDistribution Coordinate p hp hpone)
          (fun mask ↦ Includes mask (required context)) := by
      apply Finset.sum_congr rfl
      intro context _
      exact congrArg (fun probability : ℝ ↦ value context * probability)
        (eventMass_includes_maskDistribution p hp hpone
          (required context)).symm
    _ = ∑ mask : Mask Coordinate,
        (maskDistribution Coordinate p hp hpone).mass mask *
          ∑ context,
            if Includes mask (required context) then value context else 0 := by
      unfold eventMass
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro mask _
      apply Finset.sum_congr rfl
      intro context _
      by_cases hincludes : Includes mask (required context) <;>
        simp [hincludes]
      ring

end

end PegSeparation.External.LarsenYuAdaptiveSampling
