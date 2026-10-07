import PegSeparation.CFLNotPEG.External.Assumptions


open scoped BigOperators

namespace PegSeparation.External.LarsenYuBernoulli

noncomputable section

abbrev Mask (Coordinate : Type) := Coordinate → Bool

def maskMass {Coordinate : Type} [Fintype Coordinate]
    (p : ℝ) (mask : Mask Coordinate) : ℝ :=
  ∏ coordinate : Coordinate, if mask coordinate then p else 1 - p

def maskDistribution (Coordinate : Type) [Fintype Coordinate] [DecidableEq Coordinate]
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1) :
    FiniteDistribution (Mask Coordinate) where
  mass := maskMass p
  mass_nonnegative := by
    intro mask
    unfold maskMass
    apply Finset.prod_nonneg
    intro coordinate _hcoordinate
    cases mask coordinate <;> simp <;> linarith
  mass_sum := by
    change (∑ mask : Coordinate → Bool,
      ∏ coordinate : Coordinate,
        if mask coordinate then p else 1 - p) = 1
    rw [← Fintype.prod_sum (fun (_ : Coordinate) (bit : Bool) ↦
      if bit = true then p else 1 - p)]
    simp

@[simp]
theorem maskDistribution_mass
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (mask : Mask Coordinate) :
    (maskDistribution Coordinate p hp hpone).mass mask = maskMass p mask :=
  rfl

def toFinDistribution (Outcome : Type) [Fintype Outcome]
    (distribution : FiniteDistribution Outcome) :
    FiniteDistribution (Fin (Fintype.card Outcome)) where
  mass := fun index ↦ distribution.mass ((Fintype.equivFin Outcome).symm index)
  mass_nonnegative := fun index ↦
    distribution.mass_nonnegative ((Fintype.equivFin Outcome).symm index)
  mass_sum := by
    simpa using ((Fintype.equivFin Outcome).symm.sum_comp distribution.mass).trans
      distribution.mass_sum

def decodeFinSeed (Outcome : Type) [Fintype Outcome]
    (index : Fin (Fintype.card Outcome)) : Outcome :=
  (Fintype.equivFin Outcome).symm index

@[simp]
theorem toFinDistribution_mass
    (Outcome : Type) [Fintype Outcome]
    (distribution : FiniteDistribution Outcome)
    (index : Fin (Fintype.card Outcome)) :
    (toFinDistribution Outcome distribution).mass index =
      distribution.mass (decodeFinSeed Outcome index) :=
  rfl

theorem decodeFinSeed_surjective (Outcome : Type) [Fintype Outcome] :
    Function.Surjective (decodeFinSeed Outcome) :=
  (Fintype.equivFin Outcome).symm.surjective

abbrev TwoMask (Coordinate : Type) := Mask (Fin 2 × Coordinate)

def firstMask {Coordinate : Type} (mask : TwoMask Coordinate) : Mask Coordinate :=
  fun coordinate ↦ mask (0, coordinate)

def secondMask {Coordinate : Type} (mask : TwoMask Coordinate) : Mask Coordinate :=
  fun coordinate ↦ mask (1, coordinate)

end

end PegSeparation.External.LarsenYuBernoulli
