import PegSeparation.CFLNotPEG.Reduction.SCAToCellProbe
import PegSeparation.CFLNotPEG.Witness.HardSlice


namespace PegSeparation.Reduction.MultiphaseModel

open PegSeparation.CellProbe
open PegSeparation.Reduction.SCAToCellProbe

abbrev BitVector (n : ℕ) := PegSeparation.Witness.HardSlice.Vector n
abbrev IPMatrix (n : ℕ) := PegSeparation.Witness.HardSlice.Matrix n

def innerProductAnswer {n : ℕ} (S : IPMatrix n) (X : BitVector n)
    (query : Fin (PegSeparation.Witness.HardSlice.rowCount n)) : Bool :=
  decide (PegSeparation.Witness.HardSlice.vectorInnerProduct (S query) X = 1)

@[simp] theorem innerProductAnswer_eq_true_iff {n : ℕ}
    (S : IPMatrix n) (X : BitVector n)
    (query : Fin (PegSeparation.Witness.HardSlice.rowCount n)) :
    innerProductAnswer S X query = true ↔
      PegSeparation.Witness.HardSlice.vectorInnerProduct (S query) X = 1 := by
  simp [innerProductAnswer]

def runUpdateList {n wordBits updateReads updateWrites : ℕ}
    (update : Fin n → Bool →
      UpdateProgram wordBits Unit updateReads updateWrites) :
    FiniteMemory wordBits → List (Fin n × Bool) → FiniteMemory wordBits
  | memory, [] => memory
  | memory, (coordinate, bit) :: rest =>
      runUpdateList update
        ((update coordinate bit).execute memory).memory rest

theorem runUpdateList_append {n wordBits updateReads updateWrites : ℕ}
    (update : Fin n → Bool →
      UpdateProgram wordBits Unit updateReads updateWrites)
    (memory : FiniteMemory wordBits)
    (left right : List (Fin n × Bool)) :
    runUpdateList update memory (left ++ right) =
      runUpdateList update (runUpdateList update memory left) right := by
  induction left generalizing memory with
  | nil => rfl
  | cons invocation rest ih =>
      cases invocation with
      | mk coordinate bit =>
          exact ih (((update coordinate bit).execute memory).memory)

def runAllUpdates {n wordBits updateReads updateWrites : ℕ}
    (update : Fin n → Bool →
      UpdateProgram wordBits Unit updateReads updateWrites)
    (memory : FiniteMemory wordBits) (X : BitVector n) :
    FiniteMemory wordBits :=
  runUpdateList update memory
    (List.ofFn fun coordinate => (coordinate, X coordinate))

structure ExactMultiphaseIP
    (n wordBits updateReads updateWrites queryReads : ℕ) where
  preprocess : IPMatrix n → FiniteMemory wordBits
  update : Fin n → Bool →
    UpdateProgram wordBits Unit updateReads updateWrites
  query : Fin (PegSeparation.Witness.HardSlice.rowCount n) →
    ReadProgram wordBits Bool queryReads
  correct : ∀ (S : IPMatrix n) (X : BitVector n)
    (q : Fin (PegSeparation.Witness.HardSlice.rowCount n)),
    ((query q).execute (runAllUpdates update (preprocess S) X)).result =
      innerProductAnswer S X q

def logScale (n : ℕ) : ℕ := Nat.clog 2 (n + 1) + 1

def scaledLogBudget (scale n : ℕ) : ℕ := scale * logScale n

abbrev HasFastMultiphaseIPFamily : Prop :=
  ∃ wordScale queryScale updateReads updateWrites : ℕ,
    0 < wordScale ∧ 0 < queryScale ∧
      ∀ n : ℕ, 2 ≤ n →
        Nonempty
          (ExactMultiphaseIP n
            (scaledLogBudget wordScale n)
            updateReads updateWrites
            (scaledLogBudget queryScale n))

end PegSeparation.Reduction.MultiphaseModel
