import PegSeparation.CFLNotPEG.Witness.LanguageCFG


namespace PegSeparation.Closure

open PegSeparation.Witness.LanguageCFG


def reversedRecordWord (r : Record) : Word := (recordWord r).reverse

def reversedRecordsWord (rs : List Record) : Word :=
  rs.flatMap reversedRecordWord

@[simp] theorem reversedRecordsWord_nil : reversedRecordsWord [] = [] := rfl

@[simp] theorem reversedRecordsWord_cons (r : Record) (rs : List Record) :
    reversedRecordsWord (r :: rs) =
      reversedRecordWord r ++ reversedRecordsWord rs := by
  simp [reversedRecordsWord]

theorem recordsWord_append (rs ts : List Record) :
    recordsWord (rs ++ ts) = recordsWord rs ++ recordsWord ts := by
  simp [recordsWord]

@[simp] theorem reversedRecordsWord_append (rs ts : List Record) :
    reversedRecordsWord (rs ++ ts) =
      reversedRecordsWord rs ++ reversedRecordsWord ts := by
  simp [reversedRecordsWord]

@[simp] theorem bitWord_reverse (u : List Bit) :
    (bitWord u).reverse = bitWord u.reverse := by
  simp [bitWord]

theorem reversedRecordWord_eq (r : Record) :
    reversedRecordWord r =
      [.rangle] ++ bitWord r.payload.reverse ++ [.colon] ++
        bitWord r.key.reverse ++ [.langle] := by
  simp [reversedRecordWord, recordWord, List.reverse_append]

theorem recordsWord_reverse (rs : List Record) :
    (recordsWord rs).reverse = reversedRecordsWord rs.reverse := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp [recordsWord_cons, List.reverse_append, ih, reversedRecordWord]

theorem reversedRecordsWord_reverse (rs : List Record) :
    (reversedRecordsWord rs).reverse = recordsWord rs.reverse := by
  have := congrArg List.reverse (recordsWord_reverse rs.reverse)
  simpa using this.symm


def CFirst : Language Terminal := fun w =>
  ∃ (r : Record) (rest : List Record) (x q : List Bit),
    r.Valid ∧ (∀ t ∈ rest, t.Valid) ∧ x ≠ [] ∧ q ≠ [] ∧
    w = recordsWord (r :: rest) ++ suffixWord x q ∧
    r.key.reverse = q ∧
    r.payload.length = x.length ∧
    innerProduct r.payload.reverse x = 1

def Pref : Language Terminal := fun w => w.reverse ∈ CFirst

@[simp] theorem mem_pref_iff (w : Word) : w ∈ Pref ↔ w.reverse ∈ CFirst :=
  Iff.rfl

def ReversedRecord : Language Terminal := fun w =>
  ∃ r : Record, r.Valid ∧ w = reversedRecordWord r

def RegularTail : Language Terminal := fun w =>
  ∃ rs : List Record, (∀ r ∈ rs, r.Valid) ∧ w = reversedRecordsWord rs


def Shape : Language Terminal := fun w =>
  ∃ (a b : List Bit) (rs : List Record),
    a ≠ [] ∧ b ≠ [] ∧ (∀ r ∈ rs, r.Valid) ∧
    w = bitWord a ++ [.hash] ++ bitWord b ++ [.dollar] ++
      reversedRecordsWord rs

def StarWitness : Language Terminal := Pref + ReversedRecord

@[simp] theorem mem_starWitness_iff (w : Word) :
    w ∈ StarWitness ↔ w ∈ Pref ∨ w ∈ ReversedRecord :=
  Iff.rfl


theorem mem_pref_iff_explicit (w : Word) :
    w ∈ Pref ↔
      ∃ (r : Record) (rest : List Record) (x q : List Bit),
        r.Valid ∧ (∀ t ∈ rest, t.Valid) ∧ x ≠ [] ∧ q ≠ [] ∧
        w = bitWord q.reverse ++ [.hash] ++ bitWord x.reverse ++ [.dollar] ++
          reversedRecordsWord rest.reverse ++ reversedRecordWord r ∧
        r.key.reverse = q ∧
        r.payload.length = x.length ∧
        innerProduct r.payload.reverse x = 1 := by
  constructor
  · rintro ⟨r, rest, x, q, hr, hrest, hx, hq, hw, hkey, hlen, hip⟩
    refine ⟨r, rest, x, q, hr, hrest, hx, hq, ?_, hkey, hlen, hip⟩
    have := congrArg List.reverse hw
    rw [List.reverse_reverse] at this
    rw [this]
    simp [suffixWord, recordsWord_cons, List.reverse_append,
      recordsWord_reverse, reversedRecordWord, List.append_assoc]
  · rintro ⟨r, rest, x, q, hr, hrest, hx, hq, hw, hkey, hlen, hip⟩
    refine ⟨r, rest, x, q, hr, hrest, hx, hq, ?_, hkey, hlen, hip⟩
    rw [hw]
    simp [suffixWord, recordsWord_cons, List.reverse_append,
      reversedRecordsWord_reverse, reversedRecordWord, List.append_assoc]

end PegSeparation.Closure
