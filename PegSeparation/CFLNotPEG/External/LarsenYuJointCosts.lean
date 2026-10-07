import PegSeparation.CFLNotPEG.External.LarsenYuFiniteMarkov
import PegSeparation.CFLNotPEG.External.LarsenYuUpperBounds


open scoped BigOperators

namespace PegSeparation.External.LarsenYuJointCosts

noncomputable section

open LarsenYuBernoulliEvents LarsenYuFiniteMarkov

def productDistribution
    (First Second : Type) [Fintype First] [Fintype Second]
    (first : FiniteDistribution First) (second : FiniteDistribution Second) :
    FiniteDistribution (First × Second) where
  mass := fun pair ↦ first.mass pair.1 * second.mass pair.2
  mass_nonnegative := fun pair ↦
    mul_nonneg (first.mass_nonnegative pair.1) (second.mass_nonnegative pair.2)
  mass_sum := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ firstOutcome : First, ∑ secondOutcome : Second,
          first.mass firstOutcome * second.mass secondOutcome) =
          ∑ firstOutcome : First,
            first.mass firstOutcome * (∑ secondOutcome : Second,
              second.mass secondOutcome) := by
        apply Finset.sum_congr rfl
        intro firstOutcome _hfirstOutcome
        rw [Finset.mul_sum]
      _ = 1 := by simp [second.mass_sum, first.mass_sum]

namespace CellProbe.StaticStructure

variable {Input Query : Type} [Fintype Input] [Fintype Query]
  {wordBits cacheCells maxUpdatedCells : Nat}

def jointTotalCost
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells) (pair : Input × Query) : ℝ :=
  (dataStructure.probeTrace pair.1 pair.2).length

def jointUpdatedCost
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells) (pair : Input × Query) : ℝ :=
  dataStructure.updatedProbeCount pair.1 pair.2

theorem expectation_jointTotalCost
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    expectation (productDistribution Input Query inputDistribution queryDistribution)
        (jointTotalCost dataStructure) =
      dataStructure.expectedTotalProbes inputDistribution queryDistribution := by
  unfold expectation productDistribution jointTotalCost
    PegSeparation.CellProbe.StaticStructure.expectedTotalProbes
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro input _hinput
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro query _hquery
  ring

theorem expectation_jointUpdatedCost
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    expectation (productDistribution Input Query inputDistribution queryDistribution)
        (jointUpdatedCost dataStructure) =
      dataStructure.expectedUpdatedProbes inputDistribution queryDistribution := by
  unfold expectation productDistribution jointUpdatedCost
    PegSeparation.CellProbe.StaticStructure.expectedUpdatedProbes
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro input _hinput
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro query _hquery
  ring

theorem joint_bad_cost_mass_le_half
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    eventMass
        (productDistribution Input Query inputDistribution queryDistribution)
        (fun pair ↦
          4 * dataStructure.expectedTotalProbes
              inputDistribution queryDistribution <
            (jointTotalCost dataStructure) pair ∨
          4 * dataStructure.expectedUpdatedProbes
              inputDistribution queryDistribution <
            (jointUpdatedCost dataStructure) pair) ≤
      (1 / 2 : ℝ) := by
  have h := eventMass_two_bad_le_half
    (productDistribution Input Query inputDistribution queryDistribution)
    (jointTotalCost dataStructure) (jointUpdatedCost dataStructure)
    (fun pair ↦ by unfold jointTotalCost; positivity)
    (fun pair ↦ by unfold jointUpdatedCost; positivity)
  rw [expectation_jointTotalCost, expectation_jointUpdatedCost] at h
  exact h

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuJointCosts
