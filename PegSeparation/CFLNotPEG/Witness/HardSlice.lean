import PegSeparation.CFLNotPEG.Witness.LanguageCFG


namespace PegSeparation.Witness.HardSlice


abbrev Alphabet := LanguageCFG.Terminal
abbrev Word := LanguageCFG.Word
abbrev Record := LanguageCFG.Record

def bitWord (xs : List Bool) : Word := LanguageCFG.bitWord xs

structure Descriptor where
  records : List Record
  x : List Bool
  query : List Bool
  deriving DecidableEq, Repr

def encodeRecord (r : Record) : Word := LanguageCFG.recordWord r

def encodeRecords : List Record → Word
  | [] => []
  | r :: rs => encodeRecord r ++ encodeRecords rs

def encodeDescriptor (d : Descriptor) : Word :=
  encodeRecords d.records ++
    .dollar ::
      (bitWord d.x ++ .hash :: bitWord d.query)

@[simp] theorem encodeRecords_eq_recordsWord (rs : List Record) :
    encodeRecords rs = LanguageCFG.recordsWord rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [encodeRecords, encodeRecord, LanguageCFG.recordsWord, ih]

theorem encodeDescriptor_eq_languageWord (d : Descriptor) :
    encodeDescriptor d =
      LanguageCFG.recordsWord d.records ++ LanguageCFG.suffixWord d.x d.query := by
  simp [encodeDescriptor, LanguageCFG.suffixWord, bitWord, List.append_assoc]


mutual
  def scanRecords : Word → List Record → Option Descriptor
    | .langle :: rest, recordsRev => scanKey rest recordsRev []
    | .dollar :: rest, recordsRev => scanX rest recordsRev.reverse []
    | _, _ => none

  def scanKey : Word → List Record → List Bool → Option Descriptor
    | .bit0 :: rest, recordsRev, keyRev =>
        scanKey rest recordsRev (false :: keyRev)
    | .bit1 :: rest, recordsRev, keyRev =>
        scanKey rest recordsRev (true :: keyRev)
    | .colon :: rest, recordsRev, keyRev =>
        scanPayload rest recordsRev keyRev.reverse []
    | _, _, _ => none

  def scanPayload :
      Word → List Record → List Bool → List Bool → Option Descriptor
    | .bit0 :: rest, recordsRev, key, payloadRev =>
        scanPayload rest recordsRev key (false :: payloadRev)
    | .bit1 :: rest, recordsRev, key, payloadRev =>
        scanPayload rest recordsRev key (true :: payloadRev)
    | .rangle :: rest, recordsRev, key, payloadRev =>
        scanRecords rest ({ key := key, payload := payloadRev.reverse } :: recordsRev)
    | _, _, _, _ => none

  def scanX : Word → List Record → List Bool → Option Descriptor
    | .bit0 :: rest, records, xRev => scanX rest records (false :: xRev)
    | .bit1 :: rest, records, xRev => scanX rest records (true :: xRev)
    | .hash :: rest, records, xRev => scanQuery rest records xRev.reverse []
    | _, _, _ => none

  def scanQuery :
      Word → List Record → List Bool → List Bool → Option Descriptor
    | [], records, x, queryRev =>
        some { records := records, x := x, query := queryRev.reverse }
    | .bit0 :: rest, records, x, queryRev =>
        scanQuery rest records x (false :: queryRev)
    | .bit1 :: rest, records, x, queryRev =>
        scanQuery rest records x (true :: queryRev)
    | _, _, _, _ => none
end

def parseDescriptor (w : Word) : Option Descriptor := scanRecords w []

private theorem scanQuery_bitWord (q queryRev : List Bool)
    (records : List Record) (x : List Bool) :
    scanQuery (bitWord q) records x queryRev =
      some { records := records, x := x, query := queryRev.reverse ++ q } := by
  induction q generalizing queryRev with
  | nil => simp [bitWord, scanQuery]
  | cons b q ih =>
      cases b <;>
        simp only [bitWord, LanguageCFG.bitWord_cons, LanguageCFG.bitTerminal, scanQuery] <;>
        change scanQuery (bitWord q) records x (_ :: queryRev) = _ <;>
        rw [ih] <;>
        simp [List.reverse_cons, List.append_assoc]

private theorem scanX_bitWord (xs query : List Bool) (xRev : List Bool)
    (records : List Record) :
    scanX (bitWord xs ++ .hash :: bitWord query) records xRev =
      some {
        records := records
        x := xRev.reverse ++ xs
        query := query
      } := by
  induction xs generalizing xRev with
  | nil =>
      change scanQuery (bitWord query) records xRev.reverse [] = _
      rw [scanQuery_bitWord]
      simp
  | cons b xs ih =>
      cases b <;>
        simp only [bitWord, LanguageCFG.bitWord_cons, LanguageCFG.bitTerminal,
          List.cons_append, scanX] <;>
        change scanX (bitWord xs ++ .hash :: bitWord query) records (_ :: xRev) = _ <;>
        rw [ih] <;>
        simp [List.reverse_cons, List.append_assoc]

private theorem scanPayload_bitWord (payload : List Bool) (payloadRev : List Bool)
    (recordsRev : List Record) (key : List Bool) (tail : Word) :
    scanPayload (bitWord payload ++ .rangle :: tail)
        recordsRev key payloadRev =
      scanRecords tail
        ({ key := key, payload := payloadRev.reverse ++ payload } :: recordsRev) := by
  induction payload generalizing payloadRev with
  | nil => simp [bitWord, scanPayload]
  | cons b payload ih =>
      cases b <;>
        simp only [bitWord, LanguageCFG.bitWord_cons, LanguageCFG.bitTerminal,
          List.cons_append, scanPayload] <;>
        change
          scanPayload (bitWord payload ++ .rangle :: tail)
            recordsRev key (_ :: payloadRev) = _ <;>
        rw [ih] <;>
        simp [List.reverse_cons, List.append_assoc]

private theorem scanKey_bitWord (key : List Bool) (keyRev : List Bool)
    (payload : List Bool) (recordsRev : List Record) (tail : Word) :
    scanKey
        (bitWord key ++ .colon ::
          (bitWord payload ++ .rangle :: tail))
        recordsRev keyRev =
      scanRecords tail
        ({ key := keyRev.reverse ++ key, payload := payload } :: recordsRev) := by
  induction key generalizing keyRev with
  | nil =>
      change
        scanPayload (bitWord payload ++ .rangle :: tail)
          recordsRev keyRev.reverse [] = _
      rw [scanPayload_bitWord]
      simp
  | cons b key ih =>
      cases b <;>
        simp only [bitWord, LanguageCFG.bitWord_cons, LanguageCFG.bitTerminal,
          List.cons_append, scanKey] <;>
        change
          scanKey
            (bitWord key ++ .colon ::
              (bitWord payload ++ .rangle :: tail))
            recordsRev (_ :: keyRev) = _ <;>
        rw [ih] <;>
        simp [List.reverse_cons, List.append_assoc]

private theorem scanRecords_encodeRecord (r : Record) (recordsRev : List Record)
    (tail : Word) :
    scanRecords (encodeRecord r ++ tail) recordsRev =
      scanRecords tail (r :: recordsRev) := by
  cases r with
  | mk key payload =>
      have hword :
          encodeRecord { key := key, payload := payload } =
            .langle ::
              (bitWord key ++ .colon :: (bitWord payload ++ [.rangle])) := by
        simp [encodeRecord, LanguageCFG.recordWord, bitWord, List.append_assoc]
      rw [hword]
      simp only [List.cons_append, scanRecords]
      simpa [List.append_assoc] using
        (scanKey_bitWord key [] payload recordsRev tail)

private theorem scanRecords_encodeRecords (rs recordsRev : List Record)
    (xs query : List Bool) :
    scanRecords
        (encodeRecords rs ++
          .dollar ::
            (bitWord xs ++ .hash :: bitWord query))
        recordsRev =
      some {
        records := recordsRev.reverse ++ rs
        x := xs
        query := query
      } := by
  induction rs generalizing recordsRev with
  | nil => simp [encodeRecords, scanRecords, scanX_bitWord]
  | cons r rs ih =>
      simp only [encodeRecords, List.append_assoc, scanRecords_encodeRecord]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

@[simp] theorem parseDescriptor_encode (d : Descriptor) :
    parseDescriptor (encodeDescriptor d) = some d := by
  cases d with
  | mk records x query =>
      unfold parseDescriptor encodeDescriptor
      simpa only [List.reverse_nil, List.nil_append] using
        (scanRecords_encodeRecords records [] x query)

theorem encodeDescriptor_injective : Function.Injective encodeDescriptor := by
  intro d₁ d₂ h
  have h' := congrArg parseDescriptor h
  simpa using h'


abbrev F₂ := ZMod 2

def Descriptor.NonemptyFields (d : Descriptor) : Prop :=
  d.records ≠ [] ∧
    (∀ r ∈ d.records, r.key ≠ [] ∧ r.payload ≠ []) ∧
    d.x ≠ [] ∧ d.query ≠ []

def Descriptor.Accepting (d : Descriptor) : Prop :=
  d.NonemptyFields ∧
    ∃ r ∈ d.records,
      r.key.reverse = d.query ∧
      r.payload.length = d.x.length ∧
      LanguageCFG.innerProduct r.payload.reverse d.x = 1

theorem mem_languageCFG_C_iff (w : Word) :
    w ∈ LanguageCFG.C ↔
      ∃ d : Descriptor, d.Accepting ∧ encodeDescriptor d = w := by
  constructor
  · rintro ⟨rs, x, q, hrs, hvalid, hx, hq, hword,
      r, hr, hkey, hlen, hip⟩
    refine ⟨{ records := rs, x := x, query := q }, ?_, ?_⟩
    · exact ⟨⟨hrs, hvalid, hx, hq⟩, ⟨r, hr, hkey, hlen, hip⟩⟩
    · rw [encodeDescriptor_eq_languageWord]
      exact hword.symm
  · rintro ⟨d, ⟨⟨hrs, hvalid, hx, hq⟩,
      r, hr, hkey, hlen, hip⟩, hword⟩
    refine ⟨d.records, d.x, d.query, hrs, hvalid, hx, hq, ?_,
      r, hr, hkey, hlen, hip⟩
    rw [← encodeDescriptor_eq_languageWord]
    exact hword.symm


def rowCount (n : Nat) : Nat := n ^ 2

def keyWidth (n : Nat) : Nat := Nat.clog 2 (rowCount n + 1)

def binaryBE {width : Nat} (x : BitVec width) : List Bool :=
  List.ofFn fun i => x.getMsb i

@[simp] theorem binaryBE_length {width : Nat} (x : BitVec width) :
    (binaryBE x).length = width := by
  simp [binaryBE]

theorem binaryBE_injective {width : Nat} :
    Function.Injective (binaryBE : BitVec width → List Bool) := by
  intro x y h
  have hfun : (fun i : Fin width => x.getMsb i) = fun i => y.getMsb i :=
    List.ofFn_injective h
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hi' := congrFun hfun (Fin.rev ⟨i, hi⟩)
  have hindex : width - 1 - (width - (i + 1)) = i := by omega
  simpa [BitVec.getMsb_eq_getLsb, hindex] using hi'

private theorem rowNumber_fits {n : Nat} (i : Fin (rowCount n)) :
    i.val + 1 < 2 ^ keyWidth n := by
  have hi : i.val + 1 < rowCount n + 1 := by omega
  have hbound : rowCount n + 1 ≤ 2 ^ keyWidth n := by
    simpa [keyWidth] using Nat.le_pow_clog (b := 2) (by omega) (rowCount n + 1)
  exact hi.trans_le hbound

def indexBits (n : Nat) (i : Fin (rowCount n)) : List Bool :=
  binaryBE (BitVec.ofNat (keyWidth n) (i.val + 1))

@[simp] theorem indexBits_length (n : Nat) (i : Fin (rowCount n)) :
    (indexBits n i).length = keyWidth n := by
  simp [indexBits]

theorem indexBits_toNat (n : Nat) (i : Fin (rowCount n)) :
    (BitVec.ofNat (keyWidth n) (i.val + 1)).toNat = i.val + 1 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rowNumber_fits i)]

theorem indexBits_injective (n : Nat) : Function.Injective (indexBits n) := by
  intro i j h
  have hbv :
      BitVec.ofNat (keyWidth n) (i.val + 1) =
        BitVec.ofNat (keyWidth n) (j.val + 1) :=
    binaryBE_injective h
  have hnat := congrArg BitVec.toNat hbv
  rw [indexBits_toNat n i, indexBits_toNat n j] at hnat
  apply Fin.ext
  omega


abbrev Vector (n : Nat) := Fin n → Bool
abbrev Matrix (n : Nat) := Fin (rowCount n) → Vector n

def vectorInnerProduct {n : Nat} (u v : Vector n) : F₂ :=
  LanguageCFG.innerProduct (List.ofFn u) (List.ofFn v)

def hardRecord {n : Nat} (S : Matrix n) (i : Fin (rowCount n)) : Record :=
  {
    key := (indexBits n i).reverse
    payload := (List.ofFn (S i)).reverse
  }

def hardRecords {n : Nat} (S : Matrix n) : List Record :=
  List.ofFn fun i => hardRecord S i

def hardDescriptor {n : Nat} (S : Matrix n) (X : Vector n)
    (q : Fin (rowCount n)) : Descriptor :=
  {
    records := hardRecords S
    x := List.ofFn X
    query := indexBits n q
  }

def hardWord {n : Nat} (S : Matrix n) (X : Vector n)
    (q : Fin (rowCount n)) : Word :=
  encodeDescriptor (hardDescriptor S X q)

private theorem dimension_pos {n : Nat} (q : Fin (rowCount n)) : 0 < n := by
  have hq : q.val < rowCount n := q.isLt
  have hN : 0 < rowCount n := by omega
  simpa [rowCount, pow_two] using Nat.pos_of_mul_pos_right hN

private theorem keyWidth_pos {n : Nat} (q : Fin (rowCount n)) : 0 < keyWidth n := by
  apply Nat.clog_pos (by omega)
  have hq : q.val < rowCount n := q.isLt
  have hN : 0 < rowCount n := by omega
  omega

private theorem indexBits_ne_nil {n : Nat} (q i : Fin (rowCount n)) :
    indexBits n i ≠ [] := by
  apply List.ne_nil_of_length_pos
  simp [keyWidth_pos q]

private theorem vectorList_ne_nil {n : Nat} (q : Fin (rowCount n)) (v : Vector n) :
    List.ofFn v ≠ [] := by
  apply List.ne_nil_of_length_pos
  simp [dimension_pos q]

private theorem hardDescriptor_nonemptyFields {n : Nat} (S : Matrix n) (X : Vector n)
    (q : Fin (rowCount n)) : (hardDescriptor S X q).NonemptyFields := by
  have hq : q.val < rowCount n := q.isLt
  have hN : 0 < rowCount n := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply List.ne_nil_of_length_pos
    simp [hardDescriptor, hardRecords, hN]
  · intro r hr
    rw [hardDescriptor] at hr
    simp only [hardRecords, List.mem_ofFn] at hr
    rcases hr with ⟨i, hir⟩
    rw [← hir]
    constructor
    · simpa [hardRecord] using indexBits_ne_nil q i
    · simpa [hardRecord] using vectorList_ne_nil q (S i)
  · exact vectorList_ne_nil q X
  · exact indexBits_ne_nil q q

private theorem hardDescriptor_accepting_iff {n : Nat} (S : Matrix n) (X : Vector n)
    (q : Fin (rowCount n)) :
    (hardDescriptor S X q).Accepting ↔ vectorInnerProduct (S q) X = 1 := by
  constructor
  · intro h
    rcases h.2 with ⟨r, hr, hkey, _hlen, hip⟩
    rw [hardDescriptor] at hr
    simp only [hardRecords, List.mem_ofFn] at hr
    rcases hr with ⟨i, hir⟩
    rw [← hir] at hkey hip
    have hiq : i = q := by
      apply indexBits_injective n
      simpa [hardRecord, hardDescriptor] using hkey
    subst i
    simpa [hardRecord, hardDescriptor, vectorInnerProduct] using hip
  · intro hip
    refine ⟨hardDescriptor_nonemptyFields S X q, ?_⟩
    refine ⟨hardRecord S q, ?_, ?_, ?_, ?_⟩
    · simp [hardDescriptor, hardRecords]
    · simp [hardRecord, hardDescriptor]
    · simp [hardRecord, hardDescriptor]
    · simpa [hardRecord, hardDescriptor, vectorInnerProduct] using hip

theorem hardWord_mem_C_iff {n : Nat} (S : Matrix n) (X : Vector n)
    (q : Fin (rowCount n)) :
    hardWord S X q ∈ LanguageCFG.C ↔ vectorInnerProduct (S q) X = 1 := by
  rw [mem_languageCFG_C_iff]
  constructor
  · rintro ⟨d, hd, hencode⟩
    have hdEq : d = hardDescriptor S X q := by
      apply encodeDescriptor_injective
      simpa [hardWord] using hencode
    subst d
    exact (hardDescriptor_accepting_iff S X q).mp hd
  · intro hip
    refine ⟨hardDescriptor S X q, ?_, rfl⟩
    exact (hardDescriptor_accepting_iff S X q).mpr hip

end PegSeparation.Witness.HardSlice
