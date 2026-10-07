import Mathlib


namespace PegSeparation.Witness.LanguageCFG

inductive Terminal where
  | bit0 | bit1
  | langle | colon | rangle | dollar | hash
  deriving DecidableEq, Fintype, Repr

abbrev Bit := Bool
abbrev Word := List Terminal

def bitTerminal : Bit → Terminal
  | false => .bit0
  | true => .bit1

def bitWord (u : List Bit) : Word := u.map bitTerminal

@[simp] theorem bitWord_nil : bitWord [] = [] := rfl
@[simp] theorem bitWord_cons (b : Bit) (u : List Bit) :
    bitWord (b :: u) = bitTerminal b :: bitWord u := rfl
@[simp] theorem bitWord_append (u v : List Bit) :
    bitWord (u ++ v) = bitWord u ++ bitWord v := by
  simp [bitWord]

structure Record where
  key : List Bit
  payload : List Bit
  deriving DecidableEq, Repr

def Record.Valid (r : Record) : Prop := r.key ≠ [] ∧ r.payload ≠ []

def recordWord (r : Record) : Word :=
  [.langle] ++ bitWord r.key ++ [.colon] ++ bitWord r.payload ++ [.rangle]

def recordsWord (rs : List Record) : Word := rs.flatMap recordWord

@[simp] theorem recordsWord_nil : recordsWord [] = [] := rfl
@[simp] theorem recordsWord_cons (r : Record) (rs : List Record) :
    recordsWord (r :: rs) = recordWord r ++ recordsWord rs := by
  simp [recordsWord]

def suffixWord (x q : List Bit) : Word :=
  [.dollar] ++ bitWord x ++ [.hash] ++ bitWord q

def bitValue : Bit → ZMod 2
  | false => 0
  | true => 1

def innerProduct : List Bit → List Bit → ZMod 2
  | a :: u, b :: v => bitValue a * bitValue b + innerProduct u v
  | _, _ => 0

@[simp] theorem innerProduct_nil_left (v : List Bit) : innerProduct [] v = 0 := by
  cases v <;> rfl

@[simp] theorem innerProduct_nil_right (u : List Bit) : innerProduct u [] = 0 := by
  cases u <;> rfl

@[simp] theorem innerProduct_cons (a b : Bit) (u v : List Bit) :
    innerProduct (a :: u) (b :: v) =
      bitValue a * bitValue b + innerProduct u v := rfl

lemma innerProduct_append_singleton {u v : List Bit} (h : u.length = v.length)
    (a b : Bit) :
    innerProduct (u ++ [a]) (v ++ [b]) =
      innerProduct u v + bitValue a * bitValue b := by
  induction u generalizing v with
  | nil =>
      have hv : v = [] := List.length_eq_zero_iff.mp h.symm
      subst v
      simp [innerProduct]
  | cons c u ih =>
      cases v with
      | nil => simp at h
      | cons d v =>
          have hsucc : Nat.succ u.length = Nat.succ v.length := by simpa using h
          have huv : u.length = v.length := Nat.succ.inj hsucc
          simp [innerProduct, ih huv, add_assoc]

lemma innerProduct_reverse_cons_append {s x : List Bit} (h : s.length = x.length)
    (a b : Bit) :
    innerProduct (List.reverse (a :: s)) (x ++ [b]) =
      innerProduct s.reverse x + bitValue a * bitValue b := by
  rw [List.reverse_cons]
  apply innerProduct_append_singleton
  simpa using h

private lemma zmod2_of_add_one_eq_zero {z : ZMod 2} (h : z + 1 = 0) : z = 1 := by
  have hz : z = -1 := eq_neg_of_add_eq_zero_left h
  simpa using hz

private lemma zmod2_of_add_one_eq_one {z : ZMod 2} (h : z + 1 = 1) : z = 0 := by
  have h' := congrArg (fun t : ZMod 2 => t - 1) h
  simpa using h'

def C : Set Word := fun w =>
  ∃ (rs : List Record) (x q : List Bit),
    rs ≠ [] ∧
    (∀ r ∈ rs, r.Valid) ∧
    x ≠ [] ∧ q ≠ [] ∧
    w = recordsWord rs ++ suffixWord x q ∧
    ∃ r ∈ rs,
      r.key.reverse = q ∧
      r.payload.length = x.length ∧
      innerProduct r.payload.reverse x = 1

def L : Set Word := fun w => w.reverse ∈ C

namespace Grammar

inductive U : Word → Prop where
  | zero : U [.bit0]
  | one : U [.bit1]
  | consZero {w} : U w → U (.bit0 :: w)
  | consOne {w} : U w → U (.bit1 :: w)

inductive E : Word → Prop where
  | record {k s} : U (bitWord k) → U (bitWord s) →
      E ([.langle] ++ bitWord k ++ [.colon] ++ bitWord s ++ [.rangle])

inductive T : Word → Prop where
  | empty : T []
  | cons {e t} : E e → T t → T (e ++ t)

inductive P : Bit → Word → Prop where
  | base {t} : T t → P false ([.rangle] ++ t ++ [.dollar])
  | zero00 {w} : P false w → P false (.bit0 :: (w ++ [.bit0]))
  | zero01 {w} : P false w → P false (.bit0 :: (w ++ [.bit1]))
  | zero10 {w} : P false w → P false (.bit1 :: (w ++ [.bit0]))
  | zero11 {w} : P true w → P false (.bit1 :: (w ++ [.bit1]))
  | one00 {w} : P true w → P true (.bit0 :: (w ++ [.bit0]))
  | one01 {w} : P true w → P true (.bit0 :: (w ++ [.bit1]))
  | one10 {w} : P true w → P true (.bit1 :: (w ++ [.bit0]))
  | one11 {w} : P false w → P true (.bit1 :: (w ++ [.bit1]))

inductive K : Word → Prop where
  | base {w} : P true w → K ([.colon] ++ w ++ [.hash])
  | wrapZero {w} : K w → K (.bit0 :: (w ++ [.bit0]))
  | wrapOne {w} : K w → K (.bit1 :: (w ++ [.bit1]))

inductive A : Word → Prop where
  | skip {e w} : E e → A w → A (e ++ w)
  | witnessZero {w} : K w → A (.langle :: (.bit0 :: (w ++ [.bit0])))
  | witnessOne {w} : K w → A (.langle :: (.bit1 :: (w ++ [.bit1])))

end Grammar

namespace Grammar

lemma U.word_ne_nil {w : Word} (h : U w) : w ≠ [] := by
  cases h <;> simp

lemma U.toBitWord {w : Word} (h : U w) :
    ∃ u : List Bit, u ≠ [] ∧ w = bitWord u := by
  induction h with
  | zero => exact ⟨[false], by simp, rfl⟩
  | one => exact ⟨[true], by simp, rfl⟩
  | consZero _ ih =>
      rcases ih with ⟨u, hu, rfl⟩
      exact ⟨false :: u, by simp, rfl⟩
  | consOne _ ih =>
      rcases ih with ⟨u, hu, rfl⟩
      exact ⟨true :: u, by simp, rfl⟩

lemma U.ofBitWord {u : List Bit} (hu : u ≠ []) : U (bitWord u) := by
  induction u with
  | nil => exact (hu rfl).elim
  | cons b u ih =>
      cases u with
      | nil =>
          cases b with
          | false => exact U.zero
          | true => exact U.one
      | cons c u =>
          have htail : c :: u ≠ [] := by simp
          cases b
          · exact U.consZero (ih htail)
          · exact U.consOne (ih htail)

lemma U.bitWord_ne_nil {u : List Bit} (h : U (bitWord u)) : u ≠ [] := by
  intro hu
  subst u
  exact h.word_ne_nil rfl

theorem U.bitWord_iff (u : List Bit) : U (bitWord u) ↔ u ≠ [] :=
  ⟨U.bitWord_ne_nil, U.ofBitWord⟩

lemma E.sound {w : Word} (h : E w) :
    ∃ r : Record, r.Valid ∧ w = recordWord r := by
  cases h with
  | record hk hs =>
      refine ⟨⟨_, _⟩, ?_, rfl⟩
      exact ⟨hk.bitWord_ne_nil, hs.bitWord_ne_nil⟩

lemma E.complete (r : Record) (hr : r.Valid) : E (recordWord r) := by
  rcases hr with ⟨hk, hs⟩
  exact E.record (U.ofBitWord hk) (U.ofBitWord hs)

lemma T.sound {w : Word} (h : T w) :
    ∃ rs : List Record, (∀ r ∈ rs, r.Valid) ∧ w = recordsWord rs := by
  induction h with
  | empty => exact ⟨[], by simp, rfl⟩
  | cons he _ ih =>
      rcases he.sound with ⟨r, hr, rfl⟩
      rcases ih with ⟨rs, hrs, rfl⟩
      refine ⟨r :: rs, ?_, ?_⟩
      · simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨hr, hrs⟩
      · simp

lemma T.complete (rs : List Record) (hrs : ∀ r ∈ rs, r.Valid) :
    T (recordsWord rs) := by
  induction rs with
  | nil => exact T.empty
  | cons r rs ih =>
      rw [recordsWord_cons]
      exact T.cons (E.complete r (hrs r (by simp)))
        (ih (fun s hs => hrs s (by simp [hs])))

def PMeaning (p : Bit) (w : Word) : Prop :=
  ∃ (s : List Bit) (rs : List Record) (x : List Bit),
    (∀ r ∈ rs, r.Valid) ∧
    s.length = x.length ∧
    innerProduct s.reverse x = bitValue p ∧
    w = bitWord s ++ [.rangle] ++ recordsWord rs ++ [.dollar] ++ bitWord x

private lemma pMeaning_wrap {r p : Bit} {w : Word} (h : PMeaning r w)
    (a b : Bit)
    (hpar : bitValue r + bitValue a * bitValue b = bitValue p) :
    PMeaning p (bitTerminal a :: (w ++ [bitTerminal b])) := by
  rcases h with ⟨s, rs, x, hrs, hlen, hip, rfl⟩
  refine ⟨a :: s, rs, x ++ [b], hrs, ?_, ?_, ?_⟩
  · simp [hlen]
  · rw [innerProduct_reverse_cons_append hlen, hip, hpar]
  · simp only [bitWord_cons, bitWord_append]
    simp [List.append_assoc]

lemma P.sound {p : Bit} {w : Word} (h : P p w) : PMeaning p w := by
  induction h with
  | base ht =>
      rcases ht.sound with ⟨rs, hrs, rfl⟩
      exact ⟨[], rs, [], hrs, rfl, by simp [bitValue], by simp⟩
  | zero00 _ ih => exact pMeaning_wrap ih false false (by decide)
  | zero01 _ ih => exact pMeaning_wrap ih false true (by decide)
  | zero10 _ ih => exact pMeaning_wrap ih true false (by decide)
  | zero11 _ ih => exact pMeaning_wrap ih true true (by decide)
  | one00 _ ih => exact pMeaning_wrap ih false false (by decide)
  | one01 _ ih => exact pMeaning_wrap ih false true (by decide)
  | one10 _ ih => exact pMeaning_wrap ih true false (by decide)
  | one11 _ ih => exact pMeaning_wrap ih true true (by decide)

private lemma exists_append_last {α : Type*} {xs : List α} (h : xs ≠ []) :
    ∃ ys y, xs = ys ++ [y] := by
  induction xs with
  | nil => exact (h rfl).elim
  | cons x xs ih =>
      cases xs with
      | nil => exact ⟨[], x, rfl⟩
      | cons y ys =>
          rcases ih (by simp) with ⟨zs, z, hz⟩
          exact ⟨x :: zs, z, by simp [hz]⟩

private lemma P.completeAux (p : Bit) (s : List Bit) (rs : List Record)
    (x : List Bit) (hrs : ∀ r ∈ rs, r.Valid)
    (hlen : s.length = x.length)
    (hip : innerProduct s.reverse x = bitValue p) :
    P p (bitWord s ++ [.rangle] ++ recordsWord rs ++ [.dollar] ++ bitWord x) := by
  induction s generalizing p x with
  | nil =>
      have hx : x = [] := List.length_eq_zero_iff.mp hlen.symm
      subst x
      cases p
      · simpa using P.base (T.complete rs hrs)
      · simp [bitValue] at hip
  | cons a s ih =>
      have hx : x ≠ [] := by
        intro hx
        subst x
        simp at hlen
      rcases exists_append_last hx with ⟨x, b, rfl⟩
      have hlen' : s.length = x.length := by simpa using hlen
      have hstep := innerProduct_reverse_cons_append hlen' a b
      rw [hstep] at hip
      cases p <;> cases a <;> cases b
      · have hd := ih false x hlen' (by simpa [bitValue] using hip)
        simpa [bitWord, bitTerminal, List.append_assoc] using P.zero00 hd
      · have hd := ih false x hlen' (by simpa [bitValue] using hip)
        simpa [bitWord, bitTerminal, List.append_assoc] using P.zero01 hd
      · have hd := ih false x hlen' (by simpa [bitValue] using hip)
        simpa [bitWord, bitTerminal, List.append_assoc] using P.zero10 hd
      · have hd := ih true x hlen' (zmod2_of_add_one_eq_zero (by simpa [bitValue] using hip))
        simpa [bitWord, bitTerminal, List.append_assoc] using P.zero11 hd
      · have hd := ih true x hlen' (by simpa [bitValue] using hip)
        simpa [bitWord, bitTerminal, List.append_assoc] using P.one00 hd
      · have hd := ih true x hlen' (by simpa [bitValue] using hip)
        simpa [bitWord, bitTerminal, List.append_assoc] using P.one01 hd
      · have hd := ih true x hlen' (by simpa [bitValue] using hip)
        simpa [bitWord, bitTerminal, List.append_assoc] using P.one10 hd
      · have hd := ih false x hlen' (zmod2_of_add_one_eq_one (by simpa [bitValue] using hip))
        simpa [bitWord, bitTerminal, List.append_assoc] using P.one11 hd

lemma P.complete {p : Bit} {w : Word} (h : PMeaning p w) : P p w := by
  rcases h with ⟨s, rs, x, hrs, hlen, hip, rfl⟩
  exact P.completeAux p s rs x hrs hlen hip

theorem P.iff_meaning (p : Bit) (w : Word) : P p w ↔ PMeaning p w :=
  ⟨P.sound, P.complete⟩

def KMeaning (w : Word) : Prop :=
  ∃ (v : List Bit) (y : Word),
    P true y ∧
    w = bitWord v ++ [.colon] ++ y ++ [.hash] ++ bitWord v.reverse

lemma K.sound {w : Word} (h : K w) : KMeaning w := by
  induction h with
  | base hp => exact ⟨[], _, hp, by simp⟩
  | wrapZero _ ih =>
      rcases ih with ⟨v, y, hp, rfl⟩
      refine ⟨false :: v, y, hp, ?_⟩
      simp [bitWord, bitTerminal, List.append_assoc]
  | wrapOne _ ih =>
      rcases ih with ⟨v, y, hp, rfl⟩
      refine ⟨true :: v, y, hp, ?_⟩
      simp [bitWord, bitTerminal, List.append_assoc]

private lemma K.completeAux (v : List Bit) {y : Word} (hy : P true y) :
    K (bitWord v ++ [.colon] ++ y ++ [.hash] ++ bitWord v.reverse) := by
  induction v with
  | nil => simpa using K.base hy
  | cons a v ih =>
      cases a
      · simpa [bitWord, bitTerminal, List.append_assoc] using K.wrapZero ih
      · simpa [bitWord, bitTerminal, List.append_assoc] using K.wrapOne ih

lemma K.complete {w : Word} (h : KMeaning w) : K w := by
  rcases h with ⟨v, y, hy, rfl⟩
  exact K.completeAux v hy

theorem K.iff_meaning (w : Word) : K w ↔ KMeaning w :=
  ⟨K.sound, K.complete⟩

private lemma innerProduct_one_left_ne_nil {s x : List Bit}
    (h : innerProduct s.reverse x = 1) : s ≠ [] := by
  intro hs
  subst s
  simp at h

private lemma innerProduct_one_right_ne_nil {s x : List Bit}
    (hlen : s.length = x.length) (h : innerProduct s.reverse x = 1) : x ≠ [] := by
  intro hx
  subst x
  have hs : s = [] := List.length_eq_zero_iff.mp hlen
  exact innerProduct_one_left_ne_nil h hs

lemma A.prefix (pre : List Record) (hpre : ∀ r ∈ pre, r.Valid)
    {w : Word} (hw : A w) : A (recordsWord pre ++ w) := by
  induction pre with
  | nil => simpa using hw
  | cons r pre ih =>
      rw [recordsWord_cons, List.append_assoc]
      exact A.skip (E.complete r (hpre r (by simp)))
        (ih (fun s hs => hpre s (by simp [hs])))

private lemma mem_split {α : Type*} {a : α} {xs : List α} (h : a ∈ xs) :
    ∃ pre post, xs = pre ++ a :: post := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨[], xs, rfl⟩
      · rcases ih h with ⟨pre, post, rfl⟩
        exact ⟨x :: pre, post, by simp⟩

lemma A.sound {w : Word} (h : A w) : C w := by
  induction h with
  | skip he _ ih =>
      rcases he.sound with ⟨r, hr, rfl⟩
      rcases ih with ⟨rs, x, q, hrsne, hrs, hx, hq, hword, witness⟩
      refine ⟨r :: rs, x, q, by simp, ?_, hx, hq, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs
        · exact hr
        · exact hrs s hs
      · rw [recordsWord_cons, hword]
        simp [List.append_assoc]
      · rcases witness with ⟨s, hs, hkey, hlen, hip⟩
        exact ⟨s, by simp [hs], hkey, hlen, hip⟩
  | witnessZero hk =>
      rcases hk.sound with ⟨v, y, hy, rfl⟩
      rcases hy.sound with ⟨s, rs, x, hrs, hlen, hip, rfl⟩
      have hs : s ≠ [] := innerProduct_one_left_ne_nil (by simpa [bitValue] using hip)
      have hx : x ≠ [] := innerProduct_one_right_ne_nil hlen (by simpa [bitValue] using hip)
      let r : Record := ⟨false :: v, s⟩
      refine ⟨r :: rs, x, (false :: v).reverse, by simp, ?_, hx, by simp, ?_, ?_⟩
      · intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact ⟨by simp, hs⟩
        · exact hrs t ht
      · simp [r, recordWord, suffixWord, bitWord, bitTerminal, recordsWord,
          List.append_assoc]
      · refine ⟨r, by simp, rfl, hlen, ?_⟩
        simpa [r, bitValue] using hip
  | witnessOne hk =>
      rcases hk.sound with ⟨v, y, hy, rfl⟩
      rcases hy.sound with ⟨s, rs, x, hrs, hlen, hip, rfl⟩
      have hs : s ≠ [] := innerProduct_one_left_ne_nil (by simpa [bitValue] using hip)
      have hx : x ≠ [] := innerProduct_one_right_ne_nil hlen (by simpa [bitValue] using hip)
      let r : Record := ⟨true :: v, s⟩
      refine ⟨r :: rs, x, (true :: v).reverse, by simp, ?_, hx, by simp, ?_, ?_⟩
      · intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact ⟨by simp, hs⟩
        · exact hrs t ht
      · simp [r, recordWord, suffixWord, bitWord, bitTerminal, recordsWord,
          List.append_assoc]
      · refine ⟨r, by simp, rfl, hlen, ?_⟩
        simpa [r, bitValue] using hip

lemma A.complete {w : Word} (h : C w) : A w := by
  rcases h with ⟨rs, x, q, hrsne, hrs, hx, hq, hword, r, hr, hkey, hlen, hip⟩
  rcases mem_split hr with ⟨pre, post, hrsplit⟩
  subst rs
  have hrvalid : r.Valid := hrs r (by simp)
  rcases hrvalid with ⟨hrkey, hrpayload⟩
  cases hkeyBits : r.key with
  | nil => exact (hrkey hkeyBits).elim
  | cons a v =>
      have hpre : ∀ t ∈ pre, t.Valid := by
        intro t ht
        exact hrs t (by simp [ht])
      have hpost : ∀ t ∈ post, t.Valid := by
        intro t ht
        exact hrs t (by simp [ht])
      have hpMeaning : PMeaning true
          (bitWord r.payload ++ [.rangle] ++ recordsWord post ++ [.dollar] ++ bitWord x) := by
        refine ⟨r.payload, post, x, hpost, hlen, ?_, rfl⟩
        simpa [bitValue] using hip
      have hp : P true
          (bitWord r.payload ++ [.rangle] ++ recordsWord post ++ [.dollar] ++ bitWord x) :=
        P.complete hpMeaning
      have hk : K
          (bitWord v ++ [.colon] ++
            (bitWord r.payload ++ [.rangle] ++ recordsWord post ++ [.dollar] ++ bitWord x) ++
            [.hash] ++ bitWord v.reverse) := K.completeAux v hp
      have ha : A
          (recordWord r ++ recordsWord post ++ suffixWord x q) := by
        rw [← hkey, hkeyBits]
        cases a
        · simpa [recordWord, suffixWord, hkeyBits, bitWord, bitTerminal,
            List.append_assoc] using A.witnessZero hk
        · simpa [recordWord, suffixWord, hkeyBits, bitWord, bitTerminal,
            List.append_assoc] using A.witnessOne hk
      rw [hword, recordsWord, List.flatMap_append]
      simpa [recordsWord, List.append_assoc] using A.prefix pre hpre ha

theorem inductive_start_iff_mem_C (w : Word) : A w ↔ w ∈ C :=
  ⟨A.sound, A.complete⟩

@[simp] theorem mem_L_iff (w : Word) : w ∈ L ↔ w.reverse ∈ C := Iff.rfl


inductive NT where
  | U | E | T | A | K | P0 | P1
  deriving DecidableEq, Fintype, Repr

inductive RuleName where
  | u0rec | u1rec | u0 | u1
  | e
  | tcons | tempty
  | askip | awitness0 | awitness1
  | kwrap0 | kwrap1 | kbase
  | p0base | p000 | p001 | p010 | p011
  | p100 | p101 | p110 | p111
  deriving DecidableEq, Fintype, Repr

abbrev GSymbol := Symbol Terminal NT
abbrev Sentential := List GSymbol

private def tm (a : Terminal) : GSymbol := .terminal a
private def nt (n : NT) : GSymbol := .nonterminal n

private def rule (input : NT) (output : Sentential) : ContextFreeRule Terminal NT :=
  ⟨input, output⟩

def production : RuleName → ContextFreeRule Terminal NT
  | .u0rec => rule .U [tm .bit0, nt .U]
  | .u1rec => rule .U [tm .bit1, nt .U]
  | .u0 => rule .U [tm .bit0]
  | .u1 => rule .U [tm .bit1]
  | .e => rule .E [tm .langle, nt .U, tm .colon, nt .U, tm .rangle]
  | .tcons => rule .T [nt .E, nt .T]
  | .tempty => rule .T []
  | .askip => rule .A [nt .E, nt .A]
  | .awitness0 => rule .A [tm .langle, tm .bit0, nt .K, tm .bit0]
  | .awitness1 => rule .A [tm .langle, tm .bit1, nt .K, tm .bit1]
  | .kwrap0 => rule .K [tm .bit0, nt .K, tm .bit0]
  | .kwrap1 => rule .K [tm .bit1, nt .K, tm .bit1]
  | .kbase => rule .K [tm .colon, nt .P1, tm .hash]
  | .p0base => rule .P0 [tm .rangle, nt .T, tm .dollar]
  | .p000 => rule .P0 [tm .bit0, nt .P0, tm .bit0]
  | .p001 => rule .P0 [tm .bit0, nt .P0, tm .bit1]
  | .p010 => rule .P0 [tm .bit1, nt .P0, tm .bit0]
  | .p011 => rule .P0 [tm .bit1, nt .P1, tm .bit1]
  | .p100 => rule .P1 [tm .bit0, nt .P1, tm .bit0]
  | .p101 => rule .P1 [tm .bit0, nt .P1, tm .bit1]
  | .p110 => rule .P1 [tm .bit1, nt .P1, tm .bit0]
  | .p111 => rule .P1 [tm .bit1, nt .P0, tm .bit1]

def grammarRules : Finset (ContextFreeRule Terminal NT) :=
  Finset.univ.image production

@[reducible] def cfg : ContextFreeGrammar Terminal where
  NT := NT
  initial := .A
  rules := grammarRules

private def terminalSymbols (w : Word) : Sentential := w.map Symbol.terminal

private lemma production_mem (name : RuleName) : production name ∈ grammarRules := by
  simp [grammarRules]

private lemma production_derives (name : RuleName) :
    cfg.Derives [nt (production name).input] (production name).output := by
  apply ContextFreeGrammar.Produces.single
  exact ⟨production name, production_mem name, ContextFreeRule.Rewrites.input_output⟩

private lemma derives_in_context {u v : Sentential} (h : cfg.Derives u v)
    (pre post : Sentential) :
    cfg.Derives (pre ++ (u ++ post)) (pre ++ (v ++ post)) :=
  (h.append_right post).append_left pre

private lemma U.toDerives {w : Word} (h : U w) :
    cfg.Derives [nt .U] (terminalSymbols w) := by
  induction h with
  | zero => simpa [production, rule, nt, tm, terminalSymbols] using
      production_derives .u0
  | one => simpa [production, rule, nt, tm, terminalSymbols] using
      production_derives .u1
  | consZero _ ih =>
      refine (production_derives .u0rec).trans ?_
      convert derives_in_context ih [tm .bit0] [] using 1 <;>
        simp [production, rule, nt, tm, terminalSymbols, List.append_nil]
  | consOne _ ih =>
      refine (production_derives .u1rec).trans ?_
      convert derives_in_context ih [tm .bit1] [] using 1 <;>
        simp [production, rule, nt, tm, terminalSymbols, List.append_nil]

private lemma E.toDerives {w : Word} (h : E w) :
    cfg.Derives [nt .E] (terminalSymbols w) := by
  cases h with
  | @record k s hk hs =>
      refine (production_derives .e).trans ?_
      let d₁ := derives_in_context hk.toDerives [tm .langle]
        [tm .colon, nt .U, tm .rangle]
      let d₂ := derives_in_context hs.toDerives
        ([tm .langle] ++ terminalSymbols (bitWord k) ++ [tm .colon]) [tm .rangle]
      exact d₁.trans (by
        simpa [production, rule, nt, tm, terminalSymbols, List.append_assoc] using d₂)

private lemma T.toDerives {w : Word} (h : T w) :
    cfg.Derives [nt .T] (terminalSymbols w) := by
  induction h with
  | empty => simpa [production, rule, nt, terminalSymbols] using
      production_derives .tempty
  | @cons e t he ht ih =>
      refine (production_derives .tcons).trans ?_
      let d₁ := derives_in_context he.toDerives [] [nt .T]
      let d₂ := derives_in_context ih (terminalSymbols e) []
      exact d₁.trans (by
        simpa [production, rule, nt, terminalSymbols, List.map_append,
          List.append_assoc] using d₂)

private lemma P.toDerives {p : Bit} {w : Word} (h : P p w) :
    cfg.Derives [nt (if p then .P1 else .P0)] (terminalSymbols w) := by
  induction h with
  | base ht =>
      refine (production_derives .p0base).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using derives_in_context ht.toDerives [tm .rangle] [tm .dollar]
  | zero00 _ ih =>
      refine (production_derives .p000).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using derives_in_context ih [tm .bit0] [tm .bit0]
  | zero01 _ ih =>
      refine (production_derives .p001).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using derives_in_context ih [tm .bit0] [tm .bit1]
  | zero10 _ ih =>
      refine (production_derives .p010).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using derives_in_context ih [tm .bit1] [tm .bit0]
  | zero11 _ ih =>
      refine (production_derives .p011).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using derives_in_context ih [tm .bit1] [tm .bit1]
  | one00 _ ih =>
      refine (production_derives .p100).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using derives_in_context ih [tm .bit0] [tm .bit0]
  | one01 _ ih =>
      refine (production_derives .p101).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using derives_in_context ih [tm .bit0] [tm .bit1]
  | one10 _ ih =>
      refine (production_derives .p110).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using derives_in_context ih [tm .bit1] [tm .bit0]
  | one11 _ ih =>
      refine (production_derives .p111).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using derives_in_context ih [tm .bit1] [tm .bit1]

private lemma K.toDerives {w : Word} (h : K w) :
    cfg.Derives [nt .K] (terminalSymbols w) := by
  induction h with
  | base hp =>
      refine (production_derives .kbase).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using derives_in_context hp.toDerives [tm .colon] [tm .hash]
  | wrapZero _ ih =>
      refine (production_derives .kwrap0).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using derives_in_context ih [tm .bit0] [tm .bit0]
  | wrapOne _ ih =>
      refine (production_derives .kwrap1).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using derives_in_context ih [tm .bit1] [tm .bit1]

private lemma A.toDerives {w : Word} (h : A w) :
    cfg.Derives [nt .A] (terminalSymbols w) := by
  induction h with
  | @skip e w he ha ih =>
      refine (production_derives .askip).trans ?_
      let d₁ := derives_in_context he.toDerives [] [nt .A]
      let d₂ := derives_in_context ih (terminalSymbols e) []
      exact d₁.trans (by
        simpa [production, rule, nt, terminalSymbols, List.map_append,
          List.append_assoc] using d₂)
  | witnessZero hk =>
      refine (production_derives .awitness0).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context hk.toDerives [tm .langle, tm .bit0] [tm .bit0]
  | witnessOne hk =>
      refine (production_derives .awitness1).trans ?_
      simpa [production, rule, nt, tm, terminalSymbols, List.map_append,
        List.append_assoc] using
        derives_in_context hk.toDerives [tm .langle, tm .bit1] [tm .bit1]

def SymbolMeaning : GSymbol → Word → Prop
  | .terminal a, w => w = [a]
  | .nonterminal .U, w => U w
  | .nonterminal .E, w => E w
  | .nonterminal .T, w => T w
  | .nonterminal .A, w => A w
  | .nonterminal .K, w => K w
  | .nonterminal .P0, w => P false w
  | .nonterminal .P1, w => P true w

def SeqMeaning : Sentential → Word → Prop
  | [], w => w = []
  | s :: ss, w =>
      ∃ u v, w = u ++ v ∧ SymbolMeaning s u ∧ SeqMeaning ss v

set_option linter.flexible false in
private lemma production_meaning (name : RuleName) {w : Word}
    (h : SeqMeaning (production name).output w) :
    SymbolMeaning (nt (production name).input) w := by
  cases name <;>
    simp [production, rule, SeqMeaning, SymbolMeaning, nt, tm] at h ⊢
  case u0rec =>
    rcases h with ⟨u, rfl, hu⟩
    exact U.consZero hu
  case u1rec =>
    rcases h with ⟨u, rfl, hu⟩
    exact U.consOne hu
  case u0 =>
    subst w
    exact U.zero
  case u1 =>
    subst w
    exact U.one
  case e =>
    rcases h with ⟨u, v, rfl, hu, hv⟩
    rcases hu.toBitWord with ⟨k, -, rfl⟩
    rcases hv.toBitWord with ⟨s, -, rfl⟩
    simpa [List.append_assoc] using E.record hu hv
  case tcons =>
    rcases h with ⟨u, v, rfl, hu, hv⟩
    exact T.cons hu hv
  case tempty =>
    subst w
    exact T.empty
  case askip =>
    rcases h with ⟨u, v, rfl, hu, hv⟩
    exact A.skip hu hv
  case awitness0 =>
    rcases h with ⟨u, rfl, hu⟩
    exact A.witnessZero hu
  case awitness1 =>
    rcases h with ⟨u, rfl, hu⟩
    exact A.witnessOne hu
  case kwrap0 =>
    rcases h with ⟨u, rfl, hu⟩
    exact K.wrapZero hu
  case kwrap1 =>
    rcases h with ⟨u, rfl, hu⟩
    exact K.wrapOne hu
  case kbase =>
    rcases h with ⟨u, rfl, hu⟩
    exact K.base hu
  case p0base =>
    rcases h with ⟨u, rfl, hu⟩
    exact P.base hu
  case p000 =>
    rcases h with ⟨u, rfl, hu⟩
    exact P.zero00 hu
  case p001 =>
    rcases h with ⟨u, rfl, hu⟩
    exact P.zero01 hu
  case p010 =>
    rcases h with ⟨u, rfl, hu⟩
    exact P.zero10 hu
  case p011 =>
    rcases h with ⟨u, rfl, hu⟩
    exact P.zero11 hu
  case p100 =>
    rcases h with ⟨u, rfl, hu⟩
    exact P.one00 hu
  case p101 =>
    rcases h with ⟨u, rfl, hu⟩
    exact P.one01 hu
  case p110 =>
    rcases h with ⟨u, rfl, hu⟩
    exact P.one10 hu
  case p111 =>
    rcases h with ⟨u, rfl, hu⟩
    exact P.one11 hu

private lemma SeqMeaning.append {u v : Sentential} {x y : Word}
    (hu : SeqMeaning u x) (hv : SeqMeaning v y) :
    SeqMeaning (u ++ v) (x ++ y) := by
  induction u generalizing x with
  | nil =>
      simp [SeqMeaning] at hu
      subst x
      simpa using hv
  | cons s ss ih =>
      rcases hu with ⟨a, b, rfl, ha, hb⟩
      refine ⟨a, b ++ y, by simp [List.append_assoc], ha, ?_⟩
      exact ih hb

private lemma SeqMeaning.split_append {u v : Sentential} {w : Word}
    (h : SeqMeaning (u ++ v) w) :
    ∃ x y, w = x ++ y ∧ SeqMeaning u x ∧ SeqMeaning v y := by
  induction u generalizing w with
  | nil =>
      exact ⟨[], w, by simp, rfl, by simpa using h⟩
  | cons s ss ih =>
      rcases h with ⟨a, b, rfl, ha, hb⟩
      rcases ih hb with ⟨x, y, rfl, hx, hy⟩
      exact ⟨a ++ x, y, by simp [List.append_assoc], ⟨a, x, rfl, ha, hx⟩, hy⟩

private lemma SeqMeaning.singleton {s : GSymbol} {w : Word}
    (h : SymbolMeaning s w) : SeqMeaning [s] w := by
  exact ⟨w, [], by simp, h, rfl⟩

private lemma produces_preserves_meaning {u v : Sentential} {w : Word}
    (huv : cfg.Produces u v) (hv : SeqMeaning v w) : SeqMeaning u w := by
  rcases huv with ⟨r, hr, hrewrite⟩
  rcases Finset.mem_image.mp hr with ⟨name, -, hname⟩
  rw [← hname] at hrewrite
  rcases hrewrite.exists_parts with ⟨pre, post, rfl, rfl⟩
  have hv' : SeqMeaning (pre ++ ((production name).output ++ post)) w := by
    simpa [List.append_assoc] using hv
  rcases SeqMeaning.split_append (u := pre)
      (v := (production name).output ++ post) hv' with
    ⟨wp, wrest, hword, hp, hrest⟩
  rw [hword]
  rcases SeqMeaning.split_append (u := (production name).output)
      (v := post) hrest with ⟨wr, wq, hrestWord, hright, hq⟩
  rw [hrestWord]
  have hleft : SymbolMeaning (nt (production name).input) wr :=
    production_meaning name hright
  have hmiddle : SeqMeaning [nt (production name).input] wr :=
    SeqMeaning.singleton hleft
  have hpmiddle : SeqMeaning (pre ++ [nt (production name).input]) (wp ++ wr) :=
    hp.append hmiddle
  simpa [nt, List.append_assoc] using hpmiddle.append hq

private lemma derives_preserves_meaning {u v : Sentential}
    (huv : cfg.Derives u v) {w : Word} (hv : SeqMeaning v w) : SeqMeaning u w := by
  induction huv with
  | refl => exact hv
  | tail _ hstep ih => exact ih (produces_preserves_meaning hstep hv)

private lemma terminalSymbols_meaning (w : Word) : SeqMeaning (terminalSymbols w) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      exact ⟨[a], w, rfl, rfl, ih⟩

theorem mem_cfg_language_iff (w : Word) : w ∈ cfg.language ↔ A w := by
  rw [ContextFreeGrammar.mem_language_iff]
  constructor
  · intro h
    have hs : SeqMeaning [nt .A] w :=
      derives_preserves_meaning h (terminalSymbols_meaning w)
    simpa [SeqMeaning, SymbolMeaning, nt] using hs
  · exact fun h => h.toDerives

theorem cfg_language_eq_C : cfg.language = C := by
  ext w
  exact (mem_cfg_language_iff w).trans (inductive_start_iff_mem_C w)

theorem C_isContextFree : Language.IsContextFree (C : Language Terminal) :=
  ⟨cfg, cfg_language_eq_C⟩

theorem L_isContextFree : Language.IsContextFree (L : Language Terminal) := by
  change (Language.reverse (C : Language Terminal)).IsContextFree
  exact C_isContextFree.reverse

end Grammar

end PegSeparation.Witness.LanguageCFG
