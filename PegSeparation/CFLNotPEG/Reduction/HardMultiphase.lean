import PegSeparation.CFLNotPEG.Reduction.SCAToCellProbe
import PegSeparation.CFLNotPEG.Witness.HardSlice


namespace PegSeparation.Reduction.HardMultiphase

open PegSeparation.Scaffolding
open PegSeparation.Witness
open PegSeparation.Witness.HardSlice
open PegSeparation.Reduction.SCAToCellProbe

def hardPhaseI {n : Nat} (S : Matrix n) : Word :=
  encodeRecords (hardRecords S) ++ [.dollar]

def hardUpdates {n : Nat} (X : Vector n) : Word :=
  bitWord (List.ofFn X)

def hardQuerySuffix {n : Nat} (q : Fin (rowCount n)) : Word :=
  .hash :: bitWord (indexBits n q)

@[simp] theorem hardWord_eq_parts {n : Nat}
    (S : Matrix n) (X : Vector n) (q : Fin (rowCount n)) :
    hardWord S X q =
      hardPhaseI S ++ hardUpdates X ++ hardQuerySuffix q := by
  simp [hardWord, hardDescriptor, encodeDescriptor, hardPhaseI, hardUpdates,
    hardQuerySuffix, List.append_assoc]

@[simp] theorem bitWord_length (xs : List Bool) :
    (bitWord xs).length = xs.length := by
  simp [bitWord, LanguageCFG.bitWord]

@[simp] theorem encodeRecord_length (r : Record) :
    (encodeRecord r).length = r.key.length + r.payload.length + 3 := by
  simp [encodeRecord, LanguageCFG.recordWord, LanguageCFG.bitWord]
  omega

@[simp] theorem encodeRecords_length (rs : List Record) :
    (encodeRecords rs).length =
      (rs.map fun r => r.key.length + r.payload.length + 3).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [encodeRecords, List.length_append, encodeRecord_length,
        List.map_cons, List.sum_cons, ih]

@[simp] theorem hardRecord_key_length {n : Nat} (S : Matrix n)
    (i : Fin (rowCount n)) :
    (hardRecord S i).key.length = keyWidth n := by
  simp [hardRecord]

@[simp] theorem hardRecord_payload_length {n : Nat} (S : Matrix n)
    (i : Fin (rowCount n)) :
    (hardRecord S i).payload.length = n := by
  simp [hardRecord]

theorem encodeHardRecords_length {n : Nat} (S : Matrix n) :
    (encodeRecords (hardRecords S)).length =
      rowCount n * (keyWidth n + n + 3) := by
  rw [encodeRecords_length]
  simp only [hardRecords, List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    hardRecord_key_length, hardRecord_payload_length]
  simp

@[simp] theorem hardPhaseI_length {n : Nat} (S : Matrix n) :
    (hardPhaseI S).length =
      rowCount n * (keyWidth n + n + 3) + 1 := by
  simp only [hardPhaseI, List.length_append, encodeHardRecords_length,
    List.length_singleton]

@[simp] theorem hardUpdates_length {n : Nat} (X : Vector n) :
    (hardUpdates X).length = n := by
  simp [hardUpdates]

@[simp] theorem hardQuerySuffix_length {n : Nat}
    (q : Fin (rowCount n)) :
    (hardQuerySuffix q).length = keyWidth n + 1 := by
  simp [hardQuerySuffix, Nat.add_comm]

theorem keyWidth_eq_indexWidth (n : Nat) :
    keyWidth n = SCAToCellProbe.indexWidth n := rfl

theorem hardMultiphase_execution_exact
    {stateCount workLabelCount degree radius n : Nat}
    (automaton : Scaffolding.Automaton Alphabet
      stateCount workLabelCount degree radius)
    (S : Matrix n) (X : Vector n) (q : Fin (rowCount n)) :
    let persistent :=
      QueryOverlay.runFrom automaton (automaton.run (hardPhaseI S))
        (hardUpdates X)
    ((QueryOverlay.beginQuery persistent).run automaton
      (hardQuerySuffix q)).materialize =
        automaton.run (hardWord S X q) := by
  simpa only [hardWord_eq_parts] using
    QueryOverlay.multiphase_execution_exact automaton
      (hardPhaseI S) (hardUpdates X) (hardQuerySuffix q)

theorem accepts_parts_iff_innerProduct
    {stateCount workLabelCount degree radius n : Nat}
    (automaton : Scaffolding.Automaton Alphabet
      stateCount workLabelCount degree radius)
    (decidesC : ∀ w, automaton.Accepts w ↔ w ∈ LanguageCFG.C)
    (S : Matrix n) (X : Vector n) (q : Fin (rowCount n)) :
    automaton.Accepts
        (hardPhaseI S ++ hardUpdates X ++ hardQuerySuffix q) ↔
      vectorInnerProduct (S q) X = 1 := by
  rw [← hardWord_eq_parts]
  exact (decidesC _).trans (hardWord_mem_C_iff S X q)

end PegSeparation.Reduction.HardMultiphase
