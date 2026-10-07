import PegSeparation.CFLNotPEG.External.LarsenYuBernoulli


open scoped BigOperators

namespace PegSeparation.External.LarsenYuBernoulliEvents

noncomputable section

open LarsenYuBernoulli

def Includes {Coordinate : Type} (mask : Mask Coordinate)
    (required : Finset Coordinate) : Prop :=
  ∀ coordinate ∈ required, mask coordinate = true
local instance includesDecidable {Coordinate : Type} [Fintype Coordinate]
    [DecidableEq Coordinate] (mask : Mask Coordinate)
    (required : Finset Coordinate) : Decidable (Includes mask required) := by
  unfold Includes
  infer_instance


def eventMass {Outcome : Type} [Fintype Outcome]
    (distribution : FiniteDistribution Outcome)
    (event : Outcome → Prop) [DecidablePred event] : ℝ :=
  ∑ outcome : Outcome, distribution.mass outcome * if event outcome then 1 else 0

theorem maskMass_mul_indicator_includes
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (p : ℝ) (required : Finset Coordinate) (mask : Mask Coordinate) :
    maskMass p mask * (if Includes mask required then 1 else 0) =
      ∏ coordinate : Coordinate,
        if coordinate ∈ required then
          (if mask coordinate then p else 0)
        else
          (if mask coordinate then p else 1 - p) := by
  classical
  by_cases hincludes : Includes mask required
  · simp only [hincludes, if_true, mul_one, maskMass]
    apply Finset.prod_congr rfl
    intro coordinate _hcoordinate
    by_cases hrequired : coordinate ∈ required
    · have hselected : mask coordinate = true :=
        hincludes coordinate hrequired
      simp [hrequired, hselected]
    · simp [hrequired]
  · simp only [hincludes, if_false, mul_zero]
    simp only [Includes] at hincludes
    push Not at hincludes
    obtain ⟨coordinate, hrequired, hnotSelected⟩ := hincludes
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
    have hfalse : mask coordinate = false := Bool.eq_false_of_not_eq_true hnotSelected
    simp [hrequired, hfalse]

theorem eventMass_includes_maskDistribution
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (required : Finset Coordinate) :
    eventMass (maskDistribution Coordinate p hp hpone)
        (fun mask ↦ Includes mask required) = p ^ required.card := by
  classical
  unfold eventMass
  simp_rw [maskDistribution_mass, maskMass_mul_indicator_includes]
  rw [← Fintype.prod_sum (fun (coordinate : Coordinate) (bit : Bool) ↦
    if coordinate ∈ required then
      (if bit = true then p else 0)
    else
      (if bit = true then p else 1 - p))]
  simp

theorem eventMass_includes_toFinDistribution
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (required : Finset Coordinate) :
    eventMass
        (toFinDistribution (Mask Coordinate)
          (maskDistribution Coordinate p hp hpone))
        (fun index ↦ Includes (decodeFinSeed (Mask Coordinate) index) required) =
      p ^ required.card := by
  classical
  change (∑ index : Fin (Fintype.card (Mask Coordinate)),
    (maskDistribution Coordinate p hp hpone).mass
      ((Fintype.equivFin (Mask Coordinate)).symm index) *
      if Includes ((Fintype.equivFin (Mask Coordinate)).symm index) required
        then 1 else 0) = p ^ required.card
  calc
    _ = ∑ mask : Mask Coordinate,
        (maskDistribution Coordinate p hp hpone).mass mask *
          if Includes mask required then 1 else 0 := by
      simpa only using ((Fintype.equivFin (Mask Coordinate)).symm.sum_comp
        (fun mask ↦ (maskDistribution Coordinate p hp hpone).mass mask *
          if Includes mask required then 1 else 0))
    _ = p ^ required.card :=
      eventMass_includes_maskDistribution p hp hpone required

end

end PegSeparation.External.LarsenYuBernoulliEvents
