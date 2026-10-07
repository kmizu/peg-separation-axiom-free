import PegSeparation.CFLNotPEG.LowerBound.F2Bridge


open scoped BigOperators

namespace PegSeparation.LowerBound.BlockAdapter

open PegSeparation.Witness
open PegSeparation.LowerBound

noncomputable section

abbrev F2 := RandomCoherence.F2
abbrev F2Vec := RandomCoherence.F2Vec
abbrev RowMatrix := RandomCoherence.RowMatrix

variable {n d M : ℕ} {Outside : Type*}


def epochRows (split : Fin n ≃ Sum (Fin d) Outside)
    (rows : RowMatrix n M) : RowMatrix d M :=
  fun q i ↦ rows q (split.symm (.inl i))

def epochInput (split : Fin n ≃ Sum (Fin d) Outside)
    (full : F2Vec n) : F2Vec d :=
  fun i ↦ full (split.symm (.inl i))

def outsideInput (split : Fin n ≃ Sum (Fin d) Outside)
    (full : F2Vec n) : Outside → F2 :=
  fun o ↦ full (split.symm (.inr o))

def assembleInput (split : Fin n ≃ Sum (Fin d) Outside)
    (epoch : F2Vec d) (outside : Outside → F2) : F2Vec n :=
  fun i ↦ Sum.elim epoch outside (split i)

@[simp]
theorem epochRows_apply (split : Fin n ≃ Sum (Fin d) Outside)
    (rows : RowMatrix n M) (q : Fin M) (i : Fin d) :
    epochRows split rows q i = rows q (split.symm (.inl i)) :=
  rfl

@[simp]
theorem epochInput_assembleInput
    (split : Fin n ≃ Sum (Fin d) Outside)
    (epoch : F2Vec d) (outside : Outside → F2) :
    epochInput split (assembleInput split epoch outside) = epoch := by
  funext i
  simp [epochInput, assembleInput]

@[simp]
theorem outsideInput_assembleInput
    (split : Fin n ≃ Sum (Fin d) Outside)
    (epoch : F2Vec d) (outside : Outside → F2) :
    outsideInput split (assembleInput split epoch outside) = outside := by
  funext o
  simp [outsideInput, assembleInput]

theorem assembleInput_epochInput_outsideInput
    (split : Fin n ≃ Sum (Fin d) Outside) (full : F2Vec n) :
    assembleInput split (epochInput split full) (outsideInput split full) = full := by
  funext i
  generalize hz : split i = z
  cases z with
  | inl j =>
      have hij : split.symm (.inl j) = i := by
        rw [← hz]
        exact split.symm_apply_apply i
      simp [assembleInput, hz, epochInput, hij]
  | inr o =>
      have hio : split.symm (.inr o) = i := by
        rw [← hz]
        exact split.symm_apply_apply i
      simp [assembleInput, hz, outsideInput, hio]

def inputSplitEquiv (split : Fin n ≃ Sum (Fin d) Outside) :
    (F2Vec d × (Outside → F2)) ≃ F2Vec n where
  toFun pair := assembleInput split pair.1 pair.2
  invFun full := (epochInput split full, outsideInput split full)
  left_inv pair := by
    rcases pair with ⟨epoch, outside⟩
    apply Prod.ext
    · exact epochInput_assembleInput split epoch outside
    · exact outsideInput_assembleInput split epoch outside
  right_inv full := assembleInput_epochInput_outsideInput split full

def overwriteEpoch (split : Fin n ≃ Sum (Fin d) Outside)
    (full : F2Vec n) (epoch : F2Vec d) : F2Vec n :=
  assembleInput split epoch (outsideInput split full)

@[simp]
theorem epochInput_overwriteEpoch
    (split : Fin n ≃ Sum (Fin d) Outside)
    (full : F2Vec n) (epoch : F2Vec d) :
    epochInput split (overwriteEpoch split full epoch) = epoch := by
  simp [overwriteEpoch]

@[simp]
theorem outsideInput_overwriteEpoch
    (split : Fin n ≃ Sum (Fin d) Outside)
    (full : F2Vec n) (epoch : F2Vec d) :
    outsideInput split (overwriteEpoch split full epoch) =
      outsideInput split full := by
  simp [overwriteEpoch]

abbrev OutsideFiber (split : Fin n ≃ Sum (Fin d) Outside)
    (outside : Outside → F2) :=
  {full : F2Vec n // outsideInput split full = outside}

def overwriteEquiv (split : Fin n ≃ Sum (Fin d) Outside)
    (outside : Outside → F2) :
    F2Vec d ≃ OutsideFiber split outside where
  toFun epoch := ⟨assembleInput split epoch outside,
    outsideInput_assembleInput split epoch outside⟩
  invFun full := epochInput split full.1
  left_inv epoch := epochInput_assembleInput split epoch outside
  right_inv full := by
    apply Subtype.ext
    change assembleInput split (epochInput split full.1) outside = full.1
    exact
      (congrArg (assembleInput split (epochInput split full.1)) full.2.symm).trans
        (assembleInput_epochInput_outsideInput split full.1)


section FiniteSums

variable [Fintype Outside] [DecidableEq Outside]

theorem sum_assembleInput {A : Type*} [AddCommMonoid A]
    (split : Fin n ≃ Sum (Fin d) Outside) (f : F2Vec n → A) :
    (∑ pair : F2Vec d × (Outside → F2),
        f (assembleInput split pair.1 pair.2)) =
      ∑ full : F2Vec n, f full := by
  simpa [inputSplitEquiv] using (inputSplitEquiv split).sum_comp f

theorem sum_full_eq_sum_epoch_outside {A : Type*} [AddCommMonoid A]
    (split : Fin n ≃ Sum (Fin d) Outside) (f : F2Vec n → A) :
    (∑ full : F2Vec n, f full) =
      ∑ epoch : F2Vec d, ∑ outside : Outside → F2,
        f (assembleInput split epoch outside) := by
  calc
    (∑ full : F2Vec n, f full) =
        ∑ pair : F2Vec d × (Outside → F2),
          f (assembleInput split pair.1 pair.2) :=
      (sum_assembleInput split f).symm
    _ = ∑ epoch : F2Vec d, ∑ outside : Outside → F2,
          f (assembleInput split epoch outside) :=
      Fintype.sum_prod_type _

omit [DecidableEq Outside] in
theorem sum_epoch_eq_sum_outsideFiber {A : Type*} [AddCommMonoid A]
    (split : Fin n ≃ Sum (Fin d) Outside) (outside : Outside → F2)
    (f : F2Vec n → A) :
    (∑ epoch : F2Vec d, f (assembleInput split epoch outside)) =
      ∑ full : OutsideFiber split outside, f full.1 := by
  simpa [overwriteEquiv] using
    (overwriteEquiv split outside).sum_comp (fun full ↦ f full.1)

end FiniteSums


variable [Fintype Outside]

def outsideDot (split : Fin n ≃ Sum (Fin d) Outside)
    (row : F2Vec n) (outside : Outside → F2) : F2 :=
  ∑ o : Outside, outside o * row (split.symm (.inr o))

def outsideParity (split : Fin n ≃ Sum (Fin d) Outside)
    (rows : RowMatrix n M) (outside : Outside → F2) : Fin M → Bool :=
  fun q ↦ F2Bridge.toBool (outsideDot split (rows q) outside)

theorem dotHom_assembleInput
    (split : Fin n ≃ Sum (Fin d) Outside)
    (row : F2Vec n) (epoch : F2Vec d) (outside : Outside → F2) :
    RandomCoherence.dotHom row (assembleInput split epoch outside) =
      RandomCoherence.dotHom
          (fun i ↦ row (split.symm (.inl i))) epoch +
        outsideDot split row outside := by
  simp only [RandomCoherence.dotHom]
  calc
    (∑ i : Fin n, assembleInput split epoch outside i * row i) =
        ∑ z : Sum (Fin d) Outside,
          assembleInput split epoch outside (split.symm z) * row (split.symm z) := by
      apply Fintype.sum_equiv split
      intro i
      simp
    _ = (∑ i : Fin d, epoch i * row (split.symm (.inl i))) +
          ∑ o : Outside, outside o * row (split.symm (.inr o)) := by
      rw [Fintype.sum_sum_type]
      simp [assembleInput]
    _ = _ := rfl

theorem row_dotHom_assembleInput
    (split : Fin n ≃ Sum (Fin d) Outside)
    (rows : RowMatrix n M) (q : Fin M)
    (epoch : F2Vec d) (outside : Outside → F2) :
    RandomCoherence.dotHom (rows q) (assembleInput split epoch outside) =
      RandomCoherence.dotHom (epochRows split rows q) epoch +
        outsideDot split (rows q) outside := by
  exact dotHom_assembleInput split (rows q) epoch outside


theorem problem_value_eq_decide_full_dot
    (split : Fin n ≃ Sum (Fin d) Outside)
    (rows : RowMatrix n M) (outside : Outside → F2)
    (q : Fin M) (epoch : F2Vec d) :
    (InnerProductProblem.problem (epochRows split rows)
        (outsideParity split rows outside)).value q epoch =
      decide (RandomCoherence.dotHom (rows q)
        (assembleInput split epoch outside) = 1) := by
  rcases F2Bridge.f2_eq_zero_or_one
      (RandomCoherence.dotHom (epochRows split rows q) epoch) with hepoch | hepoch <;>
    rcases F2Bridge.f2_eq_zero_or_one
      (outsideDot split (rows q) outside) with hout | hout <;>
    simp [InnerProductProblem.problem, InnerProductProblem.signedCharacter,
      InnerProductProblem.querySign, RandomCoherence.chi,
      RandomCoherence.rowCharacter_apply, outsideParity, F2Bridge.toBool,
      row_dotHom_assembleInput, hepoch, hout, ZMod.val_one]


def hardMatrix
    (rows : RowMatrix n (HardSlice.rowCount n)) : HardSlice.Matrix n :=
  fun q ↦ F2Bridge.boolVector (rows q)

theorem problem_value_eq_hardSlice_innerProduct
    (split : Fin n ≃ Sum (Fin d) Outside)
    (rows : RowMatrix n (HardSlice.rowCount n)) (outside : Outside → F2)
    (q : Fin (HardSlice.rowCount n)) (epoch : F2Vec d) :
    (InnerProductProblem.problem (epochRows split rows)
        (outsideParity split rows outside)).value q epoch =
      decide (HardSlice.vectorInnerProduct (hardMatrix rows q)
        (F2Bridge.boolVector (assembleInput split epoch outside)) = 1) := by
  rw [problem_value_eq_decide_full_dot]
  simp [hardMatrix, F2Bridge.boolVector_innerProduct]

theorem problem_value_eq_true_iff_hardWord_mem
    (split : Fin n ≃ Sum (Fin d) Outside)
    (rows : RowMatrix n (HardSlice.rowCount n)) (outside : Outside → F2)
    (q : Fin (HardSlice.rowCount n)) (epoch : F2Vec d) :
    (InnerProductProblem.problem (epochRows split rows)
        (outsideParity split rows outside)).value q epoch = true ↔
      HardSlice.hardWord (hardMatrix rows)
        (F2Bridge.boolVector (assembleInput split epoch outside)) q ∈
          LanguageCFG.C := by
  rw [problem_value_eq_hardSlice_innerProduct]
  simp only [decide_eq_true_eq]
  exact (HardSlice.hardWord_mem_C_iff (hardMatrix rows)
    (F2Bridge.boolVector (assembleInput split epoch outside)) q).symm

end

end PegSeparation.LowerBound.BlockAdapter
