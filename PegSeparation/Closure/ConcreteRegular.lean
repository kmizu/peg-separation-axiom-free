import PegSeparation.Closure.Definitions


namespace PegSeparation.Closure

open PegSeparation.Witness.LanguageCFG

namespace ConcreteRegular


private lemma eval_mem_desc {σ : Type} (M : DFA Terminal σ) (D : σ → Language Terminal)
    (h0 : [] ∈ D M.start)
    (hstep : ∀ (s : σ) (a : Terminal) (w : Word), w ∈ D s → w ++ [a] ∈ D (M.step s a))
    (w : Word) : w ∈ D (M.eval w) := by
  induction w using List.reverseRecOn with
  | nil => simpa using h0
  | append_singleton v a ih =>
      rw [DFA.eval_append_singleton]
      exact hstep _ a v ih


inductive Scan where
  | between
  | afterOpen
  | inPayload
  | afterColon
  | inKey
  | dead
  deriving DecidableEq, Fintype

def scanStep : Scan → Terminal → Scan
  | .between, .rangle => .afterOpen
  | .afterOpen, .bit0 => .inPayload
  | .afterOpen, .bit1 => .inPayload
  | .inPayload, .bit0 => .inPayload
  | .inPayload, .bit1 => .inPayload
  | .inPayload, .colon => .afterColon
  | .afterColon, .bit0 => .inKey
  | .afterColon, .bit1 => .inKey
  | .inKey, .bit0 => .inKey
  | .inKey, .bit1 => .inKey
  | .inKey, .langle => .between
  | _, _ => .dead

private lemma scanStep_eq_between :
    ∀ (s : Scan) (a : Terminal), scanStep s a = Scan.between →
      s = Scan.inKey ∧ a = Terminal.langle := by
  decide

def openPart : Scan → Language Terminal
  | .between => fun w => w = []
  | .afterOpen => fun w => w = [.rangle]
  | .inPayload => fun w => ∃ p : List Bit, p ≠ [] ∧ w = [.rangle] ++ bitWord p
  | .afterColon => fun w => ∃ p : List Bit, p ≠ [] ∧ w = [.rangle] ++ bitWord p ++ [.colon]
  | .inKey => fun w => ∃ p k : List Bit, p ≠ [] ∧ k ≠ [] ∧
      w = [.rangle] ++ bitWord p ++ [.colon] ++ bitWord k
  | .dead => fun _ => True

private lemma mem_openPart_dead (w : Word) : w ∈ openPart .dead := trivial

private lemma openPart_inKey_langle {v : Word} (hv : v ∈ openPart .inKey) :
    v ++ [Terminal.langle] ∈ ReversedRecord := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hv
  refine ⟨⟨k.reverse, p.reverse⟩, ⟨by simpa using hk, by simpa using hp⟩, ?_⟩
  rw [reversedRecordWord_eq]
  simp [List.append_assoc]

private lemma openPart_step (s : Scan) (a : Terminal) (v : Word) (hv : v ∈ openPart s)
    (hne : scanStep s a ≠ Scan.between) : v ++ [a] ∈ openPart (scanStep s a) := by
  cases s <;> cases a <;> try exact mem_openPart_dead _
  case between.rangle =>
      have h : v = [] := hv
      subst h
      rfl
  case afterOpen.bit0 =>
      have h : v = [Terminal.rangle] := hv
      subst h
      exact ⟨[false], by simp, rfl⟩
  case afterOpen.bit1 =>
      have h : v = [Terminal.rangle] := hv
      subst h
      exact ⟨[true], by simp, rfl⟩
  case inPayload.bit0 =>
      obtain ⟨p, hp, rfl⟩ := hv
      exact ⟨p ++ [false], by simp, by simp [bitTerminal]⟩
  case inPayload.bit1 =>
      obtain ⟨p, hp, rfl⟩ := hv
      exact ⟨p ++ [true], by simp, by simp [bitTerminal]⟩
  case inPayload.colon =>
      obtain ⟨p, hp, rfl⟩ := hv
      exact ⟨p, hp, rfl⟩
  case afterColon.bit0 =>
      obtain ⟨p, hp, rfl⟩ := hv
      exact ⟨p, [false], hp, by simp, rfl⟩
  case afterColon.bit1 =>
      obtain ⟨p, hp, rfl⟩ := hv
      exact ⟨p, [true], hp, by simp, rfl⟩
  case inKey.bit0 =>
      obtain ⟨p, k, hp, hk, rfl⟩ := hv
      exact ⟨p, k ++ [false], hp, by simp, by simp [bitTerminal, List.append_assoc]⟩
  case inKey.bit1 =>
      obtain ⟨p, k, hp, hk, rfl⟩ := hv
      exact ⟨p, k ++ [true], hp, by simp, by simp [bitTerminal, List.append_assoc]⟩
  case inKey.langle => exact absurd rfl hne

def scanDesc (s : Scan) : Language Terminal :=
  fun w => ∃ (rs : List Record) (v : Word), (∀ r ∈ rs, r.Valid) ∧ v ∈ openPart s ∧
    w = reversedRecordsWord rs ++ v

private lemma nil_mem_scanDesc_between : [] ∈ scanDesc .between :=
  ⟨[], [], by simp, rfl, rfl⟩

private lemma mem_scanDesc_between_iff (w : Word) : w ∈ scanDesc .between ↔ w ∈ RegularTail := by
  constructor
  · rintro ⟨rs, v, hrs, hv, rfl⟩
    have h : v = [] := hv
    subst h
    exact ⟨rs, hrs, by simp⟩
  · rintro ⟨rs, hrs, rfl⟩
    exact ⟨rs, [], hrs, rfl, by simp⟩

private lemma scanDesc_step (s : Scan) (a : Terminal) (w : Word) (hw : w ∈ scanDesc s) :
    w ++ [a] ∈ scanDesc (scanStep s a) := by
  obtain ⟨rs, v, hrs, hv, rfl⟩ := hw
  by_cases hb : scanStep s a = Scan.between
  · obtain ⟨hs, ha⟩ := scanStep_eq_between s a hb
    subst hs
    subst ha
    obtain ⟨r, hr, hrw⟩ := openPart_inKey_langle hv
    rw [hb]
    refine ⟨rs ++ [r], [], ?_, rfl, ?_⟩
    · intro t ht
      rw [List.mem_append] at ht
      rcases ht with h | h
      · exact hrs t h
      · rw [List.mem_singleton] at h
        subst h
        exact hr
    · rw [reversedRecordsWord_append, reversedRecordsWord_cons, reversedRecordsWord_nil,
        ← hrw]
      simp [List.append_assoc]
  · exact ⟨rs, v ++ [a], hrs, openPart_step s a v hv hb, by simp [List.append_assoc]⟩


def scanDFA : DFA Terminal Scan where
  step := scanStep
  start := .between
  accept := {.between}

private lemma scan_bitWord_inPayload (p : List Bit) :
    scanDFA.evalFrom .inPayload (bitWord p) = Scan.inPayload := by
  induction p with
  | nil => rfl
  | cons b p ih => cases b <;> exact ih

private lemma scan_bitWord_inKey (k : List Bit) :
    scanDFA.evalFrom .inKey (bitWord k) = Scan.inKey := by
  induction k with
  | nil => rfl
  | cons b k ih => cases b <;> exact ih

private lemma scan_reversedRecordWord (r : Record) (hr : r.Valid) :
    scanDFA.evalFrom .between (reversedRecordWord r) = Scan.between := by
  obtain ⟨hk, hp⟩ := hr
  obtain ⟨b, p, hbp⟩ :=
    List.exists_cons_of_ne_nil (show r.payload.reverse ≠ [] by simpa using hp)
  obtain ⟨c, k, hck⟩ :=
    List.exists_cons_of_ne_nil (show r.key.reverse ≠ [] by simpa using hk)
  have h1 : scanDFA.evalFrom Scan.between [Terminal.rangle] = Scan.afterOpen := rfl
  have h2 : scanDFA.evalFrom Scan.afterOpen (bitWord (b :: p)) = Scan.inPayload := by
    cases b <;> exact scan_bitWord_inPayload p
  have h3 : scanDFA.evalFrom Scan.inPayload [Terminal.colon] = Scan.afterColon := rfl
  have h4 : scanDFA.evalFrom Scan.afterColon (bitWord (c :: k)) = Scan.inKey := by
    cases c <;> exact scan_bitWord_inKey k
  have h5 : scanDFA.evalFrom Scan.inKey [Terminal.langle] = Scan.between := rfl
  rw [reversedRecordWord_eq, hbp, hck]
  simp only [DFA.evalFrom_of_append, h1, h2, h3, h4, h5]

private lemma scan_reversedRecordsWord (rs : List Record) (h : ∀ r ∈ rs, r.Valid) :
    scanDFA.evalFrom .between (reversedRecordsWord rs) = Scan.between := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      rw [reversedRecordsWord_cons, DFA.evalFrom_of_append,
        scan_reversedRecordWord r (h r List.mem_cons_self)]
      exact ih fun t ht => h t (List.mem_cons_of_mem r ht)

private lemma scan_char (w : Word) : scanDFA.eval w = Scan.between ↔ w ∈ RegularTail := by
  constructor
  · intro hw
    have h := eval_mem_desc scanDFA scanDesc nil_mem_scanDesc_between
      (fun s a v hv => scanDesc_step s a v hv) w
    rw [hw] at h
    exact (mem_scanDesc_between_iff w).mp h
  · rintro ⟨rs, hrs, rfl⟩
    exact scan_reversedRecordsWord rs hrs


def recStep : Scan ⊕ Unit → Terminal → Scan ⊕ Unit
  | .inl .inKey, .langle => .inr ()
  | .inl s, a => .inl (scanStep s a)
  | .inr _, _ => .inl .dead

def recDFA : DFA Terminal (Scan ⊕ Unit) where
  step := recStep
  start := .inl .between
  accept := {.inr ()}

def recDesc : Scan ⊕ Unit → Language Terminal
  | .inl s => openPart s
  | .inr _ => ReversedRecord

private lemma recStep_inl (t : Scan) (b : Terminal) :
    scanStep t b ≠ Scan.between → recStep (.inl t) b = .inl (scanStep t b) := by
  revert t b
  decide

private lemma recDesc_step (s : Scan ⊕ Unit) (a : Terminal) (w : Word) (hw : w ∈ recDesc s) :
    w ++ [a] ∈ recDesc (recStep s a) := by
  cases s with
  | inr u => exact mem_openPart_dead _
  | inl t =>
      by_cases hb : scanStep t a = Scan.between
      · obtain ⟨hs, ha⟩ := scanStep_eq_between t a hb
        subst hs
        subst ha
        exact openPart_inKey_langle hw
      · rw [recStep_inl t a hb]
        exact openPart_step t a w hw hb

private lemma rec_bitWord_inPayload (p : List Bit) :
    recDFA.evalFrom (.inl .inPayload) (bitWord p) = Sum.inl Scan.inPayload := by
  induction p with
  | nil => rfl
  | cons b p ih => cases b <;> exact ih

private lemma rec_bitWord_inKey (k : List Bit) :
    recDFA.evalFrom (.inl .inKey) (bitWord k) = Sum.inl Scan.inKey := by
  induction k with
  | nil => rfl
  | cons b k ih => cases b <;> exact ih

private lemma rec_reversedRecordWord (r : Record) (hr : r.Valid) :
    recDFA.eval (reversedRecordWord r) = Sum.inr () := by
  obtain ⟨hk, hp⟩ := hr
  obtain ⟨b, p, hbp⟩ :=
    List.exists_cons_of_ne_nil (show r.payload.reverse ≠ [] by simpa using hp)
  obtain ⟨c, k, hck⟩ :=
    List.exists_cons_of_ne_nil (show r.key.reverse ≠ [] by simpa using hk)
  have h1 : recDFA.evalFrom (Sum.inl Scan.between) [Terminal.rangle] =
      Sum.inl Scan.afterOpen := rfl
  have h2 : recDFA.evalFrom (Sum.inl Scan.afterOpen) (bitWord (b :: p)) =
      Sum.inl Scan.inPayload := by
    cases b <;> exact rec_bitWord_inPayload p
  have h3 : recDFA.evalFrom (Sum.inl Scan.inPayload) [Terminal.colon] =
      Sum.inl Scan.afterColon := rfl
  have h4 : recDFA.evalFrom (Sum.inl Scan.afterColon) (bitWord (c :: k)) =
      Sum.inl Scan.inKey := by
    cases c <;> exact rec_bitWord_inKey k
  have h5 : recDFA.evalFrom (Sum.inl Scan.inKey) [Terminal.langle] = Sum.inr () := rfl
  change recDFA.evalFrom (Sum.inl Scan.between) (reversedRecordWord r) = Sum.inr ()
  rw [reversedRecordWord_eq, hbp, hck]
  simp only [DFA.evalFrom_of_append, h1, h2, h3, h4, h5]

private lemma rec_char (w : Word) : recDFA.eval w = Sum.inr () ↔ w ∈ ReversedRecord := by
  constructor
  · intro hw
    have h := eval_mem_desc recDFA recDesc rfl (fun s a v hv => recDesc_step s a v hv) w
    rw [hw] at h
    exact h
  · rintro ⟨r, hr, rfl⟩
    exact rec_reversedRecordWord r hr


inductive ShapePre where
  | preA
  | inA
  | preB
  | inB
  | deadPre
  deriving DecidableEq, Fintype

def shapeStep : ShapePre ⊕ Scan → Terminal → ShapePre ⊕ Scan
  | .inl .preA, .bit0 => .inl .inA
  | .inl .preA, .bit1 => .inl .inA
  | .inl .inA, .bit0 => .inl .inA
  | .inl .inA, .bit1 => .inl .inA
  | .inl .inA, .hash => .inl .preB
  | .inl .preB, .bit0 => .inl .inB
  | .inl .preB, .bit1 => .inl .inB
  | .inl .inB, .bit0 => .inl .inB
  | .inl .inB, .bit1 => .inl .inB
  | .inl .inB, .dollar => .inr .between
  | .inl _, _ => .inl .deadPre
  | .inr s, a => .inr (scanStep s a)

def shapeDFA : DFA Terminal (ShapePre ⊕ Scan) where
  step := shapeStep
  start := .inl .preA
  accept := {.inr .between}

def shapeDesc : ShapePre ⊕ Scan → Language Terminal
  | .inl .preA => fun w => w = []
  | .inl .inA => fun w => ∃ a : List Bit, a ≠ [] ∧ w = bitWord a
  | .inl .preB => fun w => ∃ a : List Bit, a ≠ [] ∧ w = bitWord a ++ [.hash]
  | .inl .inB => fun w => ∃ a b : List Bit, a ≠ [] ∧ b ≠ [] ∧
      w = bitWord a ++ [.hash] ++ bitWord b
  | .inl .deadPre => fun _ => True
  | .inr s => fun w => ∃ (a b : List Bit) (u : Word), a ≠ [] ∧ b ≠ [] ∧ u ∈ scanDesc s ∧
      w = bitWord a ++ [.hash] ++ bitWord b ++ [.dollar] ++ u

private lemma mem_shapeDesc_deadPre (w : Word) : w ∈ shapeDesc (.inl .deadPre) := trivial

private lemma shapeDesc_step (s : ShapePre ⊕ Scan) (a : Terminal) (w : Word)
    (hw : w ∈ shapeDesc s) : w ++ [a] ∈ shapeDesc (shapeStep s a) := by
  cases s with
  | inr t =>
      obtain ⟨x, y, u, hx, hy, hu, rfl⟩ := hw
      exact ⟨x, y, u ++ [a], hx, hy, scanDesc_step t a u hu, by simp [List.append_assoc]⟩
  | inl q =>
      cases q <;> cases a <;> try exact mem_shapeDesc_deadPre _
      case preA.bit0 =>
          have h : w = [] := hw
          subst h
          exact ⟨[false], by simp, rfl⟩
      case preA.bit1 =>
          have h : w = [] := hw
          subst h
          exact ⟨[true], by simp, rfl⟩
      case inA.bit0 =>
          obtain ⟨x, hx, rfl⟩ := hw
          exact ⟨x ++ [false], by simp, by simp [bitTerminal]⟩
      case inA.bit1 =>
          obtain ⟨x, hx, rfl⟩ := hw
          exact ⟨x ++ [true], by simp, by simp [bitTerminal]⟩
      case inA.hash =>
          obtain ⟨x, hx, rfl⟩ := hw
          exact ⟨x, hx, rfl⟩
      case preB.bit0 =>
          obtain ⟨x, hx, rfl⟩ := hw
          exact ⟨x, [false], hx, by simp, rfl⟩
      case preB.bit1 =>
          obtain ⟨x, hx, rfl⟩ := hw
          exact ⟨x, [true], hx, by simp, rfl⟩
      case inB.bit0 =>
          obtain ⟨x, y, hx, hy, rfl⟩ := hw
          exact ⟨x, y ++ [false], hx, by simp, by simp [bitTerminal, List.append_assoc]⟩
      case inB.bit1 =>
          obtain ⟨x, y, hx, hy, rfl⟩ := hw
          exact ⟨x, y ++ [true], hx, by simp, by simp [bitTerminal, List.append_assoc]⟩
      case inB.dollar =>
          obtain ⟨x, y, hx, hy, rfl⟩ := hw
          exact ⟨x, y, [], hx, hy, nil_mem_scanDesc_between, by simp⟩

private lemma shape_bitWord_inA (u : List Bit) :
    shapeDFA.evalFrom (.inl .inA) (bitWord u) = Sum.inl ShapePre.inA := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> exact ih

private lemma shape_bitWord_inB (u : List Bit) :
    shapeDFA.evalFrom (.inl .inB) (bitWord u) = Sum.inl ShapePre.inB := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> exact ih

private lemma shape_evalFrom_inr (s : Scan) (u : Word) :
    shapeDFA.evalFrom (.inr s) u = Sum.inr (scanDFA.evalFrom s u) := by
  induction u generalizing s with
  | nil => rfl
  | cons c u ih => exact ih (scanStep s c)

private lemma shape_eval_of_mem (x y : List Bit) (rs : List Record) (hx : x ≠ [])
    (hy : y ≠ []) (hrs : ∀ r ∈ rs, r.Valid) :
    shapeDFA.eval (bitWord x ++ [Terminal.hash] ++ bitWord y ++ [Terminal.dollar] ++
      reversedRecordsWord rs) = Sum.inr Scan.between := by
  obtain ⟨b, x', rfl⟩ := List.exists_cons_of_ne_nil hx
  obtain ⟨c, y', rfl⟩ := List.exists_cons_of_ne_nil hy
  have h1 : shapeDFA.evalFrom (Sum.inl ShapePre.preA) (bitWord (b :: x')) =
      Sum.inl ShapePre.inA := by
    cases b <;> exact shape_bitWord_inA x'
  have h2 : shapeDFA.evalFrom (Sum.inl ShapePre.inA) [Terminal.hash] =
      Sum.inl ShapePre.preB := rfl
  have h3 : shapeDFA.evalFrom (Sum.inl ShapePre.preB) (bitWord (c :: y')) =
      Sum.inl ShapePre.inB := by
    cases c <;> exact shape_bitWord_inB y'
  have h4 : shapeDFA.evalFrom (Sum.inl ShapePre.inB) [Terminal.dollar] =
      Sum.inr Scan.between := rfl
  change shapeDFA.evalFrom (Sum.inl ShapePre.preA) _ = Sum.inr Scan.between
  simp only [DFA.evalFrom_of_append, h1, h2, h3, h4, shape_evalFrom_inr,
    scan_reversedRecordsWord rs hrs]

private lemma shape_char (w : Word) :
    shapeDFA.eval w = Sum.inr Scan.between ↔ w ∈ Shape := by
  constructor
  · intro hw
    have h := eval_mem_desc shapeDFA shapeDesc rfl (fun s a v hv => shapeDesc_step s a v hv) w
    rw [hw] at h
    obtain ⟨x, y, u, hx, hy, hu, rfl⟩ := h
    obtain ⟨rs, hrs, rfl⟩ := (mem_scanDesc_between_iff u).mp hu
    exact ⟨x, y, rs, hx, hy, hrs, rfl⟩
  · rintro ⟨x, y, rs, hx, hy, hrs, rfl⟩
    exact shape_eval_of_mem x y rs hx hy hrs

end ConcreteRegular


open ConcreteRegular in
theorem regularTail_isRegular : RegularTail.IsRegular := by
  refine ⟨Scan, inferInstance, scanDFA, Set.ext fun w => ?_⟩
  change scanDFA.eval w ∈ ({Scan.between} : Set Scan) ↔ w ∈ RegularTail
  rw [Set.mem_singleton_iff]
  exact scan_char w

open ConcreteRegular in
theorem reversedRecord_isRegular : ReversedRecord.IsRegular := by
  refine ⟨Scan ⊕ Unit, inferInstance, recDFA, Set.ext fun w => ?_⟩
  change recDFA.eval w ∈ ({Sum.inr ()} : Set (Scan ⊕ Unit)) ↔ w ∈ ReversedRecord
  rw [Set.mem_singleton_iff]
  exact rec_char w

open ConcreteRegular in
theorem shape_isRegular : Shape.IsRegular := by
  refine ⟨ShapePre ⊕ Scan, inferInstance, shapeDFA, Set.ext fun w => ?_⟩
  change shapeDFA.eval w ∈ ({Sum.inr Scan.between} : Set (ShapePre ⊕ Scan)) ↔ w ∈ Shape
  rw [Set.mem_singleton_iff]
  exact shape_char w

end PegSeparation.Closure
