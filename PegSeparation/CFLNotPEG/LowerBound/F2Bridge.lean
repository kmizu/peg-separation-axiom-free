import PegSeparation.CFLNotPEG.LowerBound.InnerProductProblem
import PegSeparation.CFLNotPEG.Witness.HardSlice


open scoped BigOperators

namespace PegSeparation.LowerBound.F2Bridge

open PegSeparation.Witness
open PegSeparation.LowerBound

abbrev F2 := RandomCoherence.F2

def ofBool : Bool → F2 := LanguageCFG.bitValue

def toBool (x : F2) : Bool := decide (x = 1)

lemma f2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  have hx : x.val = 0 ∨ x.val = 1 := by
    have := x.val_lt
    omega
  rcases hx with hx | hx
  · left
    exact x.val_eq_zero.mp hx
  · right
    apply ZMod.val_injective 2
    simpa [ZMod.val_one] using hx

@[simp] theorem toBool_ofBool (b : Bool) : toBool (ofBool b) = b := by
  cases b <;> simp [toBool, ofBool, LanguageCFG.bitValue]

@[simp] theorem ofBool_toBool (x : F2) : ofBool (toBool x) = x := by
  rcases f2_eq_zero_or_one x with rfl | rfl <;>
    simp [toBool, ofBool, LanguageCFG.bitValue]

def boolVector {d : ℕ} (x : RandomCoherence.F2Vec d) : HardSlice.Vector d :=
  fun i => toBool (x i)

def f2Vector {d : ℕ} (x : HardSlice.Vector d) : RandomCoherence.F2Vec d :=
  fun i => ofBool (x i)

@[simp] theorem f2Vector_boolVector {d : ℕ}
    (x : RandomCoherence.F2Vec d) : f2Vector (boolVector x) = x := by
  funext i
  exact ofBool_toBool (x i)

@[simp] theorem boolVector_f2Vector {d : ℕ}
    (x : HardSlice.Vector d) : boolVector (f2Vector x) = x := by
  funext i
  exact toBool_ofBool (x i)

theorem vectorInnerProduct_eq_sum {d : ℕ}
    (u v : HardSlice.Vector d) :
    HardSlice.vectorInnerProduct u v =
      ∑ i, ofBool (u i) * ofBool (v i) := by
  induction d with
  | zero =>
      simp [HardSlice.vectorInnerProduct]
  | succ d ih =>
      rw [HardSlice.vectorInnerProduct]
      simp only [List.ofFn_succ, LanguageCFG.innerProduct_cons]
      rw [Fin.sum_univ_succ]
      change ofBool (u 0) * ofBool (v 0) +
          LanguageCFG.innerProduct
            (List.ofFn (fun i : Fin d => u i.succ))
            (List.ofFn (fun i : Fin d => v i.succ)) =
        ofBool (u 0) * ofBool (v 0) +
          ∑ i : Fin d, ofBool (u i.succ) * ofBool (v i.succ)
      congr 1
      exact ih (fun i => u i.succ) (fun i => v i.succ)

theorem boolVector_innerProduct {d : ℕ}
    (u v : RandomCoherence.F2Vec d) :
    HardSlice.vectorInnerProduct (boolVector u) (boolVector v) =
      RandomCoherence.dotHom u v := by
  rw [vectorInnerProduct_eq_sum]
  simp only [boolVector, ofBool_toBool]
  simp [RandomCoherence.dotHom, mul_comm]

theorem boolVector_innerProduct_eq_one {d : ℕ}
    (u v : RandomCoherence.F2Vec d) :
    HardSlice.vectorInnerProduct (boolVector u) (boolVector v) = 1 ↔
      RandomCoherence.dotHom u v = 1 := by
  rw [boolVector_innerProduct]

end PegSeparation.LowerBound.F2Bridge
