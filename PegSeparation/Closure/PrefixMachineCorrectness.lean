import PegSeparation.Closure.PrefixMachine


namespace PegSeparation.Closure

open PegSeparation.Witness.LanguageCFG
open PegSeparation.RealTimeTM


def encStack : List Bit → List Sym
  | [] => []
  | [b] => [encMark b]
  | b :: bs => encBit b :: encStack bs

def headSym : List Bit → Sym
  | [] => .blank
  | [b] => encMark b
  | b :: _ => encBit b

@[simp] theorem encStack_nil : encStack [] = [] := rfl

@[simp] theorem headSym_nil : headSym [] = Sym.blank := rfl

theorem encStack_singleton (b : Bit) : encStack [b] = [encMark b] := rfl

theorem encStack_cons_of_ne_nil {u : List Bit} (h : u ≠ []) (b : Bit) :
    encStack (b :: u) = encBit b :: encStack u := by
  cases u with
  | nil => exact absurd rfl h
  | cons c cs => rfl

theorem encStack_cons (b : Bit) (u : List Bit) :
    encStack (b :: u) = headSym (b :: u) :: encStack u := by
  cases u <;> rfl

theorem symRead_headSym_cons (c : Bit) (u : List Bit) :
    symRead (headSym (c :: u)) = some (c, u.isEmpty) := by
  cases u <;> cases c <;> rfl


def PushT (u : List Bit) (tape : AbsTape) : Prop :=
  tape = ⟨encStack u, .blank, []⟩

def PopT (u : List Bit) (tape : AbsTape) : Prop :=
  ∃ junk : List Sym, tape = ⟨encStack u.tail, headSym u, junk⟩

theorem applyAbs_hold {tape : AbsTape} (h : tape.focus = Sym.blank) :
    applyAbs tape .blank .stay = tape := by
  obtain ⟨l, f, r⟩ := tape
  simp only at h
  subst h
  rfl

theorem applyAbs_stay_focus (tape : AbsTape) :
    (applyAbs tape .blank .stay).focus = Sym.blank := rfl

theorem PushT.focus_blank {u : List Bit} {tape : AbsTape} (h : PushT u tape) :
    tape.focus = Sym.blank := by rw [h]

theorem PushT.hold {u : List Bit} {tape : AbsTape} (h : PushT u tape) :
    PushT u (applyAbs tape .blank .stay) := by
  rw [applyAbs_hold h.focus_blank]; exact h

theorem PushT.pushFirst {tape : AbsTape} (h : PushT [] tape) (b : Bit) :
    PushT [b] (applyAbs tape (encMark b) .right) := by
  subst h; rfl

theorem PushT.pushMore {u : List Bit} {tape : AbsTape} (hne : u ≠ [])
    (h : PushT u tape) (b : Bit) :
    PushT (b :: u) (applyAbs tape (encBit b) .right) := by
  subst h
  change (⟨encBit b :: encStack u, Sym.blank, []⟩ : AbsTape) =
    ⟨encStack (b :: u), Sym.blank, []⟩
  rw [encStack_cons_of_ne_nil hne]

theorem PopT.focus {u : List Bit} {tape : AbsTape} (h : PopT u tape) :
    tape.focus = headSym u := by
  obtain ⟨junk, rfl⟩ := h; rfl

theorem PopT.pop {u : List Bit} {tape : AbsTape} (h : PopT u tape) :
    PopT u.tail (applyAbs tape .blank .left) := by
  obtain ⟨junk, rfl⟩ := h
  cases u with
  | nil => exact ⟨junk, rfl⟩
  | cons b bs =>
      cases bs with
      | nil => exact ⟨junk, rfl⟩
      | cons c cs =>
          refine ⟨Sym.blank :: junk, ?_⟩
          change applyAbs ⟨encStack (c :: cs), headSym (b :: c :: cs), junk⟩
              .blank .left = _
          rw [encStack_cons c cs]
          rfl

theorem PushT.prepop {u : List Bit} {tape : AbsTape} (h : PushT u tape) :
    PopT u (applyAbs tape .blank .left) := by
  subst h
  cases u with
  | nil => exact ⟨[], rfl⟩
  | cons b bs =>
      refine ⟨[Sym.blank], ?_⟩
      rw [encStack_cons b bs]
      rfl

theorem symRead_focus_none {tape : AbsTape} (h : PopT [] tape) :
    symRead tape.focus = none := by
  rw [h.focus]; rfl

theorem symRead_focus_cons {c : Bit} {u : List Bit} {tape : AbsTape}
    (h : PopT (c :: u) tape) : symRead tape.focus = some (c, u.isEmpty) := by
  rw [h.focus]; exact symRead_headSym_cons c u


theorem step_start_langle (K P : AbsTape) :
    absStep ⟨.start, K, P⟩ .langle =
      ⟨.key1, applyAbs K .blank .stay, applyAbs P .blank .stay⟩ := rfl

theorem step_key1_bit (b : Bit) (K P : AbsTape) :
    absStep ⟨.key1, K, P⟩ (bitTerminal b) =
      ⟨.key2, applyAbs K (encMark b) .right, applyAbs P .blank .stay⟩ := by
  cases b <;> rfl

theorem step_key2_bit (b : Bit) (K P : AbsTape) :
    absStep ⟨.key2, K, P⟩ (bitTerminal b) =
      ⟨.key2, applyAbs K (encBit b) .right, applyAbs P .blank .stay⟩ := by
  cases b <;> rfl

theorem step_key2_colon (K P : AbsTape) :
    absStep ⟨.key2, K, P⟩ .colon =
      ⟨.pay1, applyAbs K .blank .stay, applyAbs P .blank .stay⟩ := rfl

theorem step_pay1_bit (b : Bit) (K P : AbsTape) :
    absStep ⟨.pay1, K, P⟩ (bitTerminal b) =
      ⟨.pay2, applyAbs K .blank .stay, applyAbs P (encMark b) .right⟩ := by
  cases b <;> rfl

theorem step_pay2_bit (b : Bit) (K P : AbsTape) :
    absStep ⟨.pay2, K, P⟩ (bitTerminal b) =
      ⟨.pay2, applyAbs K .blank .stay, applyAbs P (encBit b) .right⟩ := by
  cases b <;> rfl

theorem step_pay2_rangle (K P : AbsTape) :
    absStep ⟨.pay2, K, P⟩ .rangle =
      ⟨.between, applyAbs K .blank .stay, applyAbs P .blank .stay⟩ := rfl

theorem step_between_langle (K P : AbsTape) :
    absStep ⟨.between, K, P⟩ .langle =
      ⟨.skipKey1, applyAbs K .blank .stay, applyAbs P .blank .stay⟩ := rfl

theorem step_between_dollar (K P : AbsTape) :
    absStep ⟨.between, K, P⟩ .dollar =
      ⟨.xEven, applyAbs K .blank .stay, applyAbs P .blank .left⟩ := rfl

theorem step_skipKey1_bit (b : Bit) (K P : AbsTape) :
    absStep ⟨.skipKey1, K, P⟩ (bitTerminal b) =
      ⟨.skipKey2, applyAbs K .blank .stay, applyAbs P .blank .stay⟩ := by
  cases b <;> rfl

theorem step_skipKey2_bit (b : Bit) (K P : AbsTape) :
    absStep ⟨.skipKey2, K, P⟩ (bitTerminal b) =
      ⟨.skipKey2, applyAbs K .blank .stay, applyAbs P .blank .stay⟩ := by
  cases b <;> rfl

theorem step_skipKey2_colon (K P : AbsTape) :
    absStep ⟨.skipKey2, K, P⟩ .colon =
      ⟨.skipPay1, applyAbs K .blank .stay, applyAbs P .blank .stay⟩ := rfl

theorem step_skipPay1_bit (b : Bit) (K P : AbsTape) :
    absStep ⟨.skipPay1, K, P⟩ (bitTerminal b) =
      ⟨.skipPay2, applyAbs K .blank .stay, applyAbs P .blank .stay⟩ := by
  cases b <;> rfl

theorem step_skipPay2_bit (b : Bit) (K P : AbsTape) :
    absStep ⟨.skipPay2, K, P⟩ (bitTerminal b) =
      ⟨.skipPay2, applyAbs K .blank .stay, applyAbs P .blank .stay⟩ := by
  cases b <;> rfl

theorem step_skipPay2_rangle (K P : AbsTape) :
    absStep ⟨.skipPay2, K, P⟩ .rangle =
      ⟨.between, applyAbs K .blank .stay, applyAbs P .blank .stay⟩ := rfl

theorem step_x_bit (parity a c : Bit) (marked : Bool) (K P : AbsTape)
    (h : symRead P.focus = some (c, marked)) :
    absStep ⟨xStateOf parity, K, P⟩ (bitTerminal a) =
      ⟨xStateOf (xor parity (a && c)), applyAbs K .blank .stay,
        applyAbs P .blank .left⟩ := by
  cases parity <;> cases a <;>
    simp [absStep, absTrans, xStateOf, transX, transXBit, bitTerminal, h,
      popPay]

theorem step_x_bit_exhausted (parity a : Bit) (K P : AbsTape)
    (h : symRead P.focus = none) :
    (absStep ⟨xStateOf parity, K, P⟩ (bitTerminal a)).state = St.reject := by
  cases parity <;> cases a <;>
    simp [absStep, absTrans, xStateOf, transX, transXBit, bitTerminal, h,
      rejectInstr, holdBoth]

theorem step_xEven_hash (K P : AbsTape) :
    (absStep ⟨.xEven, K, P⟩ .hash).state = St.reject := by
  simp [absStep, absTrans, transX, rejectInstr, holdBoth]

theorem step_xOdd_hash (K P : AbsTape) (h : symRead P.focus = none) :
    absStep ⟨.xOdd, K, P⟩ .hash =
      ⟨.qRead, applyAbs K .blank .left, applyAbs P .blank .stay⟩ := by
  simp [absStep, absTrans, transX, h, popKey]

theorem step_xOdd_hash_pending (c : Bit) (marked : Bool) (K P : AbsTape)
    (h : symRead P.focus = some (c, marked)) :
    (absStep ⟨.xOdd, K, P⟩ .hash).state = St.reject := by
  simp [absStep, absTrans, transX, h, rejectInstr, holdBoth]

theorem step_q_match_unmarked (a : Bit) (K P : AbsTape)
    (h : symRead K.focus = some (a, false)) :
    absStep ⟨.qRead, K, P⟩ (bitTerminal a) =
      ⟨.qRead, applyAbs K .blank .left, applyAbs P .blank .stay⟩ := by
  cases a <;> simp [absStep, absTrans, transQ, transQBit, bitTerminal, h,
    popKey]

theorem step_q_match_marked (a : Bit) (K P : AbsTape)
    (h : symRead K.focus = some (a, true)) :
    absStep ⟨.qRead, K, P⟩ (bitTerminal a) =
      ⟨.accept, applyAbs K .blank .left, applyAbs P .blank .stay⟩ := by
  cases a <;> simp [absStep, absTrans, transQ, transQBit, bitTerminal, h,
    popKey]

theorem step_q_mismatch (a c : Bit) (marked : Bool) (K P : AbsTape)
    (hne : ¬ a = c) (h : symRead K.focus = some (c, marked)) :
    (absStep ⟨.qRead, K, P⟩ (bitTerminal a)).state = St.reject := by
  cases a <;> cases c <;> simp_all [absStep, absTrans, transQ, transQBit,
    bitTerminal, rejectInstr, holdBoth]

theorem step_q_exhausted (a : Bit) (K P : AbsTape)
    (h : symRead K.focus = none) :
    (absStep ⟨.qRead, K, P⟩ (bitTerminal a)).state = St.reject := by
  cases a <;> simp [absStep, absTrans, transQ, transQBit, bitTerminal, h,
    rejectInstr, holdBoth]


private theorem bitValue_xor_and (parity a c : Bit) :
    bitValue parity + bitValue c * bitValue a =
      bitValue (xor parity (a && c)) := by
  revert parity a c; decide

private theorem bitValue_injective {p q : Bit} (h : bitValue p = bitValue q) :
    p = q := by
  revert h; revert p q; decide

private theorem ne_nil_of_innerProduct_one {u x : List Bit}
    (h : innerProduct u x = 1) : x ≠ [] := by
  rintro rfl
  rw [innerProduct_nil_right] at h
  exact absurd h (by decide)

private theorem exists_concat {α : Type*} {l : List α} (h : l ≠ []) :
    ∃ (init : List α) (last : α), l = init ++ [last] := by
  induction l with
  | nil => exact absurd rfl h
  | cons a l ih =>
      cases l with
      | nil => exact ⟨[], a, rfl⟩
      | cons b l =>
          obtain ⟨init, last, hl⟩ := ih (by simp)
          exact ⟨a :: init, last, by rw [hl]; rfl⟩


def XInv (parity : Bit) (w : Word) (K P : AbsTape) : Prop :=
  ∃ (r : Record) (rest : List Record) (x consumed rem : List Bit),
    r.Valid ∧ (∀ t ∈ rest, t.Valid) ∧
    w = recordsWord (r :: rest) ++ [.dollar] ++ bitWord x ∧
    r.payload.reverse = consumed ++ rem ∧
    consumed.length = x.length ∧
    innerProduct consumed x = bitValue parity ∧
    PushT r.key.reverse K ∧ PopT rem P

def QInv (w : Word) (K : AbsTape) : Prop :=
  ∃ (r : Record) (rest : List Record) (x q rem : List Bit),
    r.Valid ∧ (∀ t ∈ rest, t.Valid) ∧
    w = recordsWord (r :: rest) ++ suffixWord x q ∧
    r.payload.length = x.length ∧
    innerProduct r.payload.reverse x = 1 ∧
    r.key.reverse = q ++ rem ∧ PopT rem K

def Inv (w : Word) : AbsConfig → Prop
  | ⟨.start, K, P⟩ => w = [] ∧ PushT [] K ∧ PushT [] P
  | ⟨.key1, K, P⟩ => w = [.langle] ∧ PushT [] K ∧ PushT [] P
  | ⟨.key2, K, P⟩ =>
      ∃ k : List Bit, k ≠ [] ∧ w = [.langle] ++ bitWord k ∧
        PushT k.reverse K ∧ PushT [] P
  | ⟨.pay1, K, P⟩ =>
      ∃ k : List Bit, k ≠ [] ∧ w = [.langle] ++ bitWord k ++ [.colon] ∧
        PushT k.reverse K ∧ PushT [] P
  | ⟨.pay2, K, P⟩ =>
      ∃ k s : List Bit, k ≠ [] ∧ s ≠ [] ∧
        w = [.langle] ++ bitWord k ++ [.colon] ++ bitWord s ∧
        PushT k.reverse K ∧ PushT s.reverse P
  | ⟨.between, K, P⟩ =>
      ∃ (r : Record) (rest : List Record), r.Valid ∧ (∀ t ∈ rest, t.Valid) ∧
        w = recordsWord (r :: rest) ∧
        PushT r.key.reverse K ∧ PushT r.payload.reverse P
  | ⟨.skipKey1, K, P⟩ =>
      ∃ (r : Record) (rest : List Record), r.Valid ∧ (∀ t ∈ rest, t.Valid) ∧
        w = recordsWord (r :: rest) ++ [.langle] ∧
        PushT r.key.reverse K ∧ PushT r.payload.reverse P
  | ⟨.skipKey2, K, P⟩ =>
      ∃ (r : Record) (rest : List Record) (k : List Bit),
        r.Valid ∧ (∀ t ∈ rest, t.Valid) ∧ k ≠ [] ∧
        w = recordsWord (r :: rest) ++ [.langle] ++ bitWord k ∧
        PushT r.key.reverse K ∧ PushT r.payload.reverse P
  | ⟨.skipPay1, K, P⟩ =>
      ∃ (r : Record) (rest : List Record) (k : List Bit),
        r.Valid ∧ (∀ t ∈ rest, t.Valid) ∧ k ≠ [] ∧
        w = recordsWord (r :: rest) ++ [.langle] ++ bitWord k ++ [.colon] ∧
        PushT r.key.reverse K ∧ PushT r.payload.reverse P
  | ⟨.skipPay2, K, P⟩ =>
      ∃ (r : Record) (rest : List Record) (k s : List Bit),
        r.Valid ∧ (∀ t ∈ rest, t.Valid) ∧ k ≠ [] ∧ s ≠ [] ∧
        w = recordsWord (r :: rest) ++ [.langle] ++ bitWord k ++ [.colon] ++
          bitWord s ∧
        PushT r.key.reverse K ∧ PushT r.payload.reverse P
  | ⟨.xEven, K, P⟩ => XInv false w K P
  | ⟨.xOdd, K, P⟩ => XInv true w K P
  | ⟨.qRead, K, _⟩ => QInv w K
  | ⟨.accept, _, _⟩ => w ∈ CFirst
  | ⟨.reject, _, _⟩ => True

private theorem inv_xStateOf (parity : Bit) (w : Word) (K P : AbsTape)
    (h : XInv parity w K P) : Inv w ⟨xStateOf parity, K, P⟩ := by
  cases parity <;> exact h

private theorem inv_of_reject_state {w : Word} {c : AbsConfig}
    (h : c.state = St.reject) : Inv w c := by
  obtain ⟨s, K, P⟩ := c
  cases s
  case reject => exact True.intro
  all_goals (exfalso; simp at h)

private theorem inv_of_eq {w : Word} {c c' : AbsConfig} (h : c = c')
    (hi : Inv w c') : Inv w c := h ▸ hi

theorem inv_init : Inv [] absInit := ⟨rfl, rfl, rfl⟩


private theorem xPhase_step (parity : Bit) (w : Word) (t : Terminal)
    (K P : AbsTape) (h : XInv parity w K P) :
    Inv (w ++ [t]) (absStep ⟨xStateOf parity, K, P⟩ t) := by
  obtain ⟨r, rest, x, consumed, rem, hr, hrest, hw, hsplit, hlen, hip, hK,
    hP⟩ := h
  subst hw
  cases rem with
  | nil =>
      have hnone : symRead P.focus = none := symRead_focus_none hP
      cases t
      case bit0 =>
        exact inv_of_reject_state (step_x_bit_exhausted parity false K P hnone)
      case bit1 =>
        exact inv_of_reject_state (step_x_bit_exhausted parity true K P hnone)
      case hash =>
        cases parity
        · exact inv_of_reject_state (step_xEven_hash K P)
        · refine inv_of_eq (step_xOdd_hash K P hnone) ?_
          have hconsumed : consumed = r.payload.reverse := by
            rw [hsplit, List.append_nil]
          refine ⟨r, rest, x, [], r.key.reverse, hr, hrest, ?_, ?_, ?_, by simp,
            hK.prepop⟩
          · simp [suffixWord, List.append_assoc]
          · have := hlen
            rw [hconsumed] at this
            simpa using this
          · rw [← hconsumed]; simpa [bitValue] using hip
      all_goals cases parity <;> exact True.intro
  | cons c rem' =>
      have hsome : symRead P.focus = some (c, rem'.isEmpty) :=
        symRead_focus_cons hP
      cases t
      case bit0 =>
        refine inv_of_eq (step_x_bit parity false c rem'.isEmpty K P hsome) ?_
        refine inv_xStateOf _ _ _ _ ?_
        refine ⟨r, rest, x ++ [false], consumed ++ [c], rem', hr, hrest, ?_, ?_,
          ?_, ?_, hK.hold, hP.pop⟩
        · simp [bitTerminal]
        · simpa [List.append_assoc] using hsplit
        · simp [hlen]
        · rw [innerProduct_append_singleton hlen, hip, bitValue_xor_and]
      case bit1 =>
        refine inv_of_eq (step_x_bit parity true c rem'.isEmpty K P hsome) ?_
        refine inv_xStateOf _ _ _ _ ?_
        refine ⟨r, rest, x ++ [true], consumed ++ [c], rem', hr, hrest, ?_, ?_,
          ?_, ?_, hK.hold, hP.pop⟩
        · simp [bitTerminal]
        · simpa [List.append_assoc] using hsplit
        · simp [hlen]
        · rw [innerProduct_append_singleton hlen, hip, bitValue_xor_and]
      case hash =>
        cases parity
        · exact inv_of_reject_state (step_xEven_hash K P)
        · exact inv_of_reject_state
            (step_xOdd_hash_pending c rem'.isEmpty K P hsome)
      all_goals cases parity <;> exact True.intro


private theorem qPhase_bit (a : Bit) (K P : AbsTape) (r : Record)
    (rest : List Record) (x q : List Bit) (c : Bit) (rem' : List Bit)
    (hr : r.Valid) (hrest : ∀ t ∈ rest, t.Valid)
    (hlen : r.payload.length = x.length)
    (hip : innerProduct r.payload.reverse x = 1)
    (hkey : r.key.reverse = q ++ c :: rem')
    (hK : PopT (c :: rem') K) :
    Inv (recordsWord (r :: rest) ++ suffixWord x q ++ [bitTerminal a])
      (absStep ⟨.qRead, K, P⟩ (bitTerminal a)) := by
  have hsome : symRead K.focus = some (c, rem'.isEmpty) := symRead_focus_cons hK
  by_cases hac : a = c
  · subst hac
    have hword : recordsWord (r :: rest) ++ suffixWord x q ++ [bitTerminal a] =
        recordsWord (r :: rest) ++ suffixWord x (q ++ [a]) := by
      simp [suffixWord, List.append_assoc]
    cases rem' with
    | nil =>
        refine inv_of_eq (step_q_match_marked a K P (by simpa using hsome)) ?_
        refine ⟨r, rest, x, q ++ [a], hr, hrest,
          ne_nil_of_innerProduct_one hip, by simp, hword, ?_, hlen, hip⟩
        simpa using hkey
    | cons d rem'' =>
        refine inv_of_eq
          (step_q_match_unmarked a K P (by simpa using hsome)) ?_
        refine ⟨r, rest, x, q ++ [a], d :: rem'', hr, hrest, hword, hlen, hip,
          ?_, hK.pop⟩
        simpa [List.append_assoc] using hkey
  · exact inv_of_reject_state (step_q_mismatch a c rem'.isEmpty K P hac hsome)

private theorem qPhase_step (w : Word) (t : Terminal) (K P : AbsTape)
    (h : QInv w K) : Inv (w ++ [t]) (absStep ⟨.qRead, K, P⟩ t) := by
  obtain ⟨r, rest, x, q, rem, hr, hrest, hw, hlen, hip, hkey, hK⟩ := h
  subst hw
  cases rem with
  | nil =>
      have hnone : symRead K.focus = none := symRead_focus_none hK
      cases t
      case bit0 => exact inv_of_reject_state (step_q_exhausted false K P hnone)
      case bit1 => exact inv_of_reject_state (step_q_exhausted true K P hnone)
      all_goals exact True.intro
  | cons c rem' =>
      cases t
      case bit0 =>
        exact qPhase_bit false K P r rest x q c rem' hr hrest hlen hip hkey hK
      case bit1 =>
        exact qPhase_bit true K P r rest x q c rem' hr hrest hlen hip hkey hK
      all_goals exact True.intro


theorem inv_step (w : Word) (t : Terminal) (c : AbsConfig) (h : Inv w c) :
    Inv (w ++ [t]) (absStep c t) := by
  obtain ⟨s, K, P⟩ := c
  cases s
  case start =>
    obtain ⟨hw, hK, hP⟩ := h
    subst hw; subst hK; subst hP
    cases t
    case langle => exact ⟨rfl, rfl, rfl⟩
    all_goals exact True.intro
  case key1 =>
    obtain ⟨hw, hK, hP⟩ := h
    subst hw; subst hK; subst hP
    cases t
    case bit0 =>
      refine inv_of_eq (step_key1_bit false _ _) ?_
      exact ⟨[false], by simp, rfl, PushT.pushFirst rfl false, rfl⟩
    case bit1 =>
      refine inv_of_eq (step_key1_bit true _ _) ?_
      exact ⟨[true], by simp, rfl, PushT.pushFirst rfl true, rfl⟩
    all_goals exact True.intro
  case key2 =>
    obtain ⟨k, hk, hw, hK, hP⟩ := h
    subst hw
    cases t
    case bit0 =>
      refine inv_of_eq (step_key2_bit false _ _) ?_
      refine ⟨k ++ [false], by simp, by simp [bitTerminal], ?_, hP.hold⟩
      simpa using PushT.pushMore (by simpa using hk) hK false
    case bit1 =>
      refine inv_of_eq (step_key2_bit true _ _) ?_
      refine ⟨k ++ [true], by simp, by simp [bitTerminal], ?_, hP.hold⟩
      simpa using PushT.pushMore (by simpa using hk) hK true
    case colon =>
      refine inv_of_eq (step_key2_colon _ _) ?_
      exact ⟨k, hk, rfl, hK.hold, hP.hold⟩
    all_goals exact True.intro
  case pay1 =>
    obtain ⟨k, hk, hw, hK, hP⟩ := h
    subst hw
    cases t
    case bit0 =>
      refine inv_of_eq (step_pay1_bit false _ _) ?_
      exact ⟨k, [false], hk, by simp, by simp [List.append_assoc, bitTerminal],
        hK.hold, PushT.pushFirst hP false⟩
    case bit1 =>
      refine inv_of_eq (step_pay1_bit true _ _) ?_
      exact ⟨k, [true], hk, by simp, by simp [List.append_assoc, bitTerminal],
        hK.hold, PushT.pushFirst hP true⟩
    all_goals exact True.intro
  case pay2 =>
    obtain ⟨k, s, hk, hs, hw, hK, hP⟩ := h
    subst hw
    cases t
    case bit0 =>
      refine inv_of_eq (step_pay2_bit false _ _) ?_
      refine ⟨k, s ++ [false], hk, by simp,
        by simp [List.append_assoc, bitTerminal], hK.hold, ?_⟩
      simpa using PushT.pushMore (by simpa using hs) hP false
    case bit1 =>
      refine inv_of_eq (step_pay2_bit true _ _) ?_
      refine ⟨k, s ++ [true], hk, by simp,
        by simp [List.append_assoc, bitTerminal], hK.hold, ?_⟩
      simpa using PushT.pushMore (by simpa using hs) hP true
    case rangle =>
      refine inv_of_eq (step_pay2_rangle _ _) ?_
      refine ⟨⟨k, s⟩, [], ⟨hk, hs⟩, by simp, ?_, hK.hold, hP.hold⟩
      simp [recordsWord, recordWord, List.append_assoc]
    all_goals exact True.intro
  case between =>
    obtain ⟨r, rest, hr, hrest, hw, hK, hP⟩ := h
    subst hw
    cases t
    case langle =>
      refine inv_of_eq (step_between_langle _ _) ?_
      exact ⟨r, rest, hr, hrest, rfl, hK.hold, hP.hold⟩
    case dollar =>
      refine inv_of_eq (step_between_dollar _ _) ?_
      refine inv_xStateOf false _ _ _ ?_
      exact ⟨r, rest, [], [], r.payload.reverse, hr, hrest, by simp, by simp,
        by simp, by simp [bitValue], hK.hold, hP.prepop⟩
    all_goals exact True.intro
  case skipKey1 =>
    obtain ⟨r, rest, hr, hrest, hw, hK, hP⟩ := h
    subst hw
    cases t
    case bit0 =>
      refine inv_of_eq (step_skipKey1_bit false _ _) ?_
      exact ⟨r, rest, [false], hr, hrest, by simp, by simp [bitTerminal],
        hK.hold, hP.hold⟩
    case bit1 =>
      refine inv_of_eq (step_skipKey1_bit true _ _) ?_
      exact ⟨r, rest, [true], hr, hrest, by simp, by simp [bitTerminal],
        hK.hold, hP.hold⟩
    all_goals exact True.intro
  case skipKey2 =>
    obtain ⟨r, rest, k, hr, hrest, hk, hw, hK, hP⟩ := h
    subst hw
    cases t
    case bit0 =>
      refine inv_of_eq (step_skipKey2_bit false _ _) ?_
      exact ⟨r, rest, k ++ [false], hr, hrest, by simp,
        by simp [List.append_assoc, bitTerminal], hK.hold, hP.hold⟩
    case bit1 =>
      refine inv_of_eq (step_skipKey2_bit true _ _) ?_
      exact ⟨r, rest, k ++ [true], hr, hrest, by simp,
        by simp [List.append_assoc, bitTerminal], hK.hold, hP.hold⟩
    case colon =>
      refine inv_of_eq (step_skipKey2_colon _ _) ?_
      exact ⟨r, rest, k, hr, hrest, hk, rfl, hK.hold, hP.hold⟩
    all_goals exact True.intro
  case skipPay1 =>
    obtain ⟨r, rest, k, hr, hrest, hk, hw, hK, hP⟩ := h
    subst hw
    cases t
    case bit0 =>
      refine inv_of_eq (step_skipPay1_bit false _ _) ?_
      exact ⟨r, rest, k, [false], hr, hrest, hk, by simp,
        by simp [List.append_assoc, bitTerminal], hK.hold, hP.hold⟩
    case bit1 =>
      refine inv_of_eq (step_skipPay1_bit true _ _) ?_
      exact ⟨r, rest, k, [true], hr, hrest, hk, by simp,
        by simp [List.append_assoc, bitTerminal], hK.hold, hP.hold⟩
    all_goals exact True.intro
  case skipPay2 =>
    obtain ⟨r, rest, k, s, hr, hrest, hk, hs, hw, hK, hP⟩ := h
    subst hw
    cases t
    case bit0 =>
      refine inv_of_eq (step_skipPay2_bit false _ _) ?_
      exact ⟨r, rest, k, s ++ [false], hr, hrest, hk, by simp,
        by simp [List.append_assoc, bitTerminal], hK.hold, hP.hold⟩
    case bit1 =>
      refine inv_of_eq (step_skipPay2_bit true _ _) ?_
      exact ⟨r, rest, k, s ++ [true], hr, hrest, hk, by simp,
        by simp [List.append_assoc, bitTerminal], hK.hold, hP.hold⟩
    case rangle =>
      refine inv_of_eq (step_skipPay2_rangle _ _) ?_
      refine ⟨r, rest ++ [⟨k, s⟩], hr, ?_, ?_, hK.hold, hP.hold⟩
      · intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hrest u hu
        · rw [List.mem_singleton.mp hu]; exact ⟨hk, hs⟩
      · simp [recordsWord, recordWord, List.append_assoc]
    all_goals exact True.intro
  case xEven => exact xPhase_step false w t K P h
  case xOdd => exact xPhase_step true w t K P h
  case qRead => exact qPhase_step w t K P h
  case accept => cases t <;> exact True.intro
  case reject => cases t <;> exact True.intro

theorem inv_absRun (w : Word) : Inv w (absRun w) := by
  induction w using List.reverseRecOn with
  | nil => exact inv_init
  | append_singleton u t ih =>
      rw [absRun_append_singleton]
      exact inv_step u t (absRun u) ih

private theorem mem_CFirst_of_inv_accept {w : Word} {c : AbsConfig}
    (hstate : c.state = St.accept) (h : Inv w c) : w ∈ CFirst := by
  obtain ⟨s, K, P⟩ := c
  cases s
  case accept => exact h
  all_goals (exfalso; simp at hstate)

theorem mem_CFirst_of_absRun_accept {w : Word}
    (h : (absRun w).state = St.accept) : w ∈ CFirst :=
  mem_CFirst_of_inv_accept h (inv_absRun w)


theorem run_key_bits (k u : List Bit) (hu : u ≠ []) (P : AbsTape)
    (hP : P.focus = Sym.blank) :
    absRunFrom ⟨.key2, ⟨encStack u, .blank, []⟩, P⟩ (bitWord k) =
      ⟨.key2, ⟨encStack (k.reverse ++ u), .blank, []⟩, P⟩ := by
  induction k generalizing u with
  | nil => simp
  | cons b k ih =>
      rw [bitWord_cons, absRunFrom_cons, step_key2_bit, applyAbs_hold hP]
      rw [show applyAbs ⟨encStack u, Sym.blank, []⟩ (encBit b) .right =
        ⟨encStack (b :: u), Sym.blank, []⟩ from PushT.pushMore hu rfl b]
      rw [ih (b :: u) (by simp)]
      simp

theorem run_pay_bits (s v : List Bit) (hv : v ≠ []) (K : AbsTape)
    (hK : K.focus = Sym.blank) :
    absRunFrom ⟨.pay2, K, ⟨encStack v, .blank, []⟩⟩ (bitWord s) =
      ⟨.pay2, K, ⟨encStack (s.reverse ++ v), .blank, []⟩⟩ := by
  induction s generalizing v with
  | nil => simp
  | cons b s ih =>
      rw [bitWord_cons, absRunFrom_cons, step_pay2_bit, applyAbs_hold hK]
      rw [show applyAbs ⟨encStack v, Sym.blank, []⟩ (encBit b) .right =
        ⟨encStack (b :: v), Sym.blank, []⟩ from PushT.pushMore hv rfl b]
      rw [ih (b :: v) (by simp)]
      simp

theorem run_skipKey_bits (k : List Bit) (K P : AbsTape)
    (hK : K.focus = Sym.blank) (hP : P.focus = Sym.blank) :
    absRunFrom ⟨.skipKey2, K, P⟩ (bitWord k) = ⟨.skipKey2, K, P⟩ := by
  induction k with
  | nil => rfl
  | cons b k ih =>
      rw [bitWord_cons, absRunFrom_cons, step_skipKey2_bit, applyAbs_hold hK,
        applyAbs_hold hP, ih]

theorem run_skipPay_bits (s : List Bit) (K P : AbsTape)
    (hK : K.focus = Sym.blank) (hP : P.focus = Sym.blank) :
    absRunFrom ⟨.skipPay2, K, P⟩ (bitWord s) = ⟨.skipPay2, K, P⟩ := by
  induction s with
  | nil => rfl
  | cons b s ih =>
      rw [bitWord_cons, absRunFrom_cons, step_skipPay2_bit, applyAbs_hold hK,
        applyAbs_hold hP, ih]

theorem run_skip_record (r : Record) (hr : r.Valid) (K P : AbsTape)
    (hK : K.focus = Sym.blank) (hP : P.focus = Sym.blank) :
    absRunFrom ⟨.between, K, P⟩ (recordWord r) = ⟨.between, K, P⟩ := by
  obtain ⟨hkne, hsne⟩ := hr
  cases hkey : r.key with
  | nil => exact absurd hkey hkne
  | cons b k =>
      cases hpay : r.payload with
      | nil => exact absurd hpay hsne
      | cons d s =>
          have hword : recordWord r =
              [Terminal.langle] ++ [bitTerminal b] ++ bitWord k ++
                [Terminal.colon] ++ [bitTerminal d] ++ bitWord s ++
                [Terminal.rangle] := by
            rw [recordWord, hkey, hpay]
            simp [List.append_assoc]
          rw [hword]
          simp only [absRunFrom_append, absRunFrom_singleton]
          rw [step_between_langle, applyAbs_hold hK, applyAbs_hold hP,
            step_skipKey1_bit, applyAbs_hold hK, applyAbs_hold hP,
            run_skipKey_bits k K P hK hP, step_skipKey2_colon,
            applyAbs_hold hK, applyAbs_hold hP, step_skipPay1_bit,
            applyAbs_hold hK, applyAbs_hold hP, run_skipPay_bits s K P hK hP,
            step_skipPay2_rangle, applyAbs_hold hK, applyAbs_hold hP]

theorem run_skip_records (rs : List Record) (hrs : ∀ t ∈ rs, t.Valid)
    (K P : AbsTape) (hK : K.focus = Sym.blank) (hP : P.focus = Sym.blank) :
    absRunFrom ⟨.between, K, P⟩ (recordsWord rs) = ⟨.between, K, P⟩ := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      rw [recordsWord_cons, absRunFrom_append,
        run_skip_record r (hrs r (by simp)) K P hK hP,
        ih (fun t ht => hrs t (by simp [ht]))]

theorem run_first_record (r : Record) (hr : r.Valid) :
    absRunFrom absInit (recordWord r) =
      ⟨.between, ⟨encStack r.key.reverse, .blank, []⟩,
        ⟨encStack r.payload.reverse, .blank, []⟩⟩ := by
  obtain ⟨hkne, hsne⟩ := hr
  cases hkey : r.key with
  | nil => exact absurd hkey hkne
  | cons b k =>
      cases hpay : r.payload with
      | nil => exact absurd hpay hsne
      | cons d s =>
          have hword : recordWord r =
              [Terminal.langle] ++ [bitTerminal b] ++ bitWord k ++
                [Terminal.colon] ++ [bitTerminal d] ++ bitWord s ++
                [Terminal.rangle] := by
            rw [recordWord, hkey, hpay]
            simp [List.append_assoc]
          have hblank : (⟨[], Sym.blank, []⟩ : AbsTape).focus = Sym.blank := rfl
          have hkeyTape : (⟨encStack (k.reverse ++ [b]), Sym.blank, []⟩ :
              AbsTape).focus = Sym.blank := rfl
          have hpayTape : (⟨encStack (s.reverse ++ [d]), Sym.blank, []⟩ :
              AbsTape).focus = Sym.blank := rfl
          have hstart : absStep absInit Terminal.langle =
              ⟨.key1, ⟨[], Sym.blank, []⟩, ⟨[], Sym.blank, []⟩⟩ := rfl
          rw [hword]
          simp only [absRunFrom_append, absRunFrom_singleton]
          rw [hstart, step_key1_bit]
          rw [applyAbs_hold hblank]
          rw [show applyAbs ⟨[], Sym.blank, []⟩ (encMark b) .right =
            ⟨encStack [b], Sym.blank, []⟩ from PushT.pushFirst rfl b]
          rw [run_key_bits k [b] (by simp) _ hblank, step_key2_colon]
          rw [applyAbs_hold hkeyTape, applyAbs_hold hblank, step_pay1_bit]
          rw [applyAbs_hold hkeyTape]
          rw [show applyAbs ⟨[], Sym.blank, []⟩ (encMark d) .right =
            ⟨encStack [d], Sym.blank, []⟩ from PushT.pushFirst rfl d]
          rw [run_pay_bits s [d] (by simp) _ hkeyTape, step_pay2_rangle]
          rw [applyAbs_hold hkeyTape, applyAbs_hold hpayTape]
          simp

theorem run_x_bits (x cs rem : List Bit) (parity target : Bit) (K P : AbsTape)
    (hlen : cs.length = x.length) (hK : K.focus = Sym.blank)
    (hP : PopT (cs ++ rem) P)
    (htarget : bitValue target = bitValue parity + innerProduct cs x) :
    ∃ P' : AbsTape, PopT rem P' ∧
      absRunFrom ⟨xStateOf parity, K, P⟩ (bitWord x) =
        ⟨xStateOf target, K, P'⟩ := by
  induction x generalizing cs parity P with
  | nil =>
      have hcs : cs = [] := List.length_eq_zero_iff.mp hlen
      subst hcs
      have : target = parity := by
        apply bitValue_injective
        simpa using htarget
      subst this
      exact ⟨P, by simpa using hP, rfl⟩
  | cons a x ih =>
      cases cs with
      | nil => simp at hlen
      | cons c cs =>
          have hPcons : PopT (c :: (cs ++ rem)) P := by simpa using hP
          have hsome : symRead P.focus = some (c, (cs ++ rem).isEmpty) :=
            symRead_focus_cons hPcons
          have hlen' : cs.length = x.length := by simpa using hlen
          have htarget' : bitValue target =
              bitValue (xor parity (a && c)) + innerProduct cs x := by
            rw [← bitValue_xor_and, add_assoc]
            simpa using htarget
          obtain ⟨P', hP', hrun⟩ :=
            ih cs (xor parity (a && c)) (applyAbs P .blank .left) hlen'
              (by simpa using hPcons.pop) htarget'
          refine ⟨P', hP', ?_⟩
          rw [bitWord_cons, absRunFrom_cons,
            step_x_bit parity a c (cs ++ rem).isEmpty K P hsome,
            applyAbs_hold hK, hrun]

theorem run_q_bits (q rem : List Bit) (hrem : rem ≠ []) (K P : AbsTape)
    (hK : PopT (q ++ rem) K) (hP : P.focus = Sym.blank) :
    ∃ K' : AbsTape, PopT rem K' ∧
      absRunFrom ⟨.qRead, K, P⟩ (bitWord q) = ⟨.qRead, K', P⟩ := by
  induction q generalizing K with
  | nil => exact ⟨K, by simpa using hK, rfl⟩
  | cons b q ih =>
      have hK' : PopT (b :: (q ++ rem)) K := by simpa using hK
      have hsome : symRead K.focus = some (b, (q ++ rem).isEmpty) :=
        symRead_focus_cons hK'
      have hne : (q ++ rem).isEmpty = false := by
        cases hqr : q ++ rem with
        | nil => exact absurd hqr (by simp [hrem])
        | cons _ _ => rfl
      rw [hne] at hsome
      obtain ⟨K'', hK'', hrun⟩ :=
        ih (applyAbs K .blank .left) (by simpa using hK'.pop)
      refine ⟨K'', hK'', ?_⟩
      rw [bitWord_cons, absRunFrom_cons,
        step_q_match_unmarked b K P hsome, applyAbs_hold hP, hrun]

theorem run_q_last (d : Bit) (K P : AbsTape) (hK : PopT [d] K) :
    (absStep ⟨.qRead, K, P⟩ (bitTerminal d)).state = St.accept := by
  have hsome : symRead K.focus = some (d, true) := by
    simpa using symRead_focus_cons (u := ([] : List Bit)) hK
  rw [step_q_match_marked d K P hsome]

theorem absRun_accept_of_mem_CFirst {w : Word} (h : w ∈ CFirst) :
    (absRun w).state = St.accept := by
  obtain ⟨r, rest, x, q, hr, hrest, hx, hq, hw, hkey, hlen, hip⟩ := h
  subst hw
  subst hkey
  have hword : recordsWord (r :: rest) ++ suffixWord x r.key.reverse =
      recordWord r ++ recordsWord rest ++ [Terminal.dollar] ++ bitWord x ++
        [Terminal.hash] ++ bitWord r.key.reverse := by
    simp [recordsWord_cons, suffixWord, List.append_assoc]
  obtain ⟨qinit, qlast, hqsplit⟩ := exists_concat hq
  have hKf : (⟨encStack r.key.reverse, Sym.blank, []⟩ : AbsTape).focus =
      Sym.blank := rfl
  have hPf : (⟨encStack r.payload.reverse, Sym.blank, []⟩ : AbsTape).focus =
      Sym.blank := rfl
  have hPpop : PopT r.payload.reverse
      (applyAbs ⟨encStack r.payload.reverse, Sym.blank, []⟩ .blank .left) :=
    PushT.prepop rfl
  have hlen' : r.payload.reverse.length = x.length := by simpa using hlen
  have htarget : bitValue true =
      bitValue false + innerProduct r.payload.reverse x := by
    rw [hip]; decide
  obtain ⟨P', hP', hrunx⟩ :=
    run_x_bits x r.payload.reverse [] false true
      ⟨encStack r.key.reverse, Sym.blank, []⟩ _ hlen' hKf
      (by simpa using hPpop) htarget
  simp only [xStateOf] at hrunx
  have hnone : symRead P'.focus = none := symRead_focus_none hP'
  obtain ⟨K', hK', hrunq⟩ :=
    run_q_bits qinit [qlast] (by simp)
      (applyAbs ⟨encStack (qinit ++ [qlast]), Sym.blank, []⟩ .blank .left)
      (applyAbs P' .blank .stay) (PushT.prepop rfl) (applyAbs_stay_focus P')
  rw [absRun, hword]
  simp only [absRunFrom_append, absRunFrom_singleton]
  rw [run_first_record r hr, run_skip_records rest hrest _ _ hKf hPf,
    step_between_dollar, applyAbs_hold hKf, hrunx,
    step_xOdd_hash _ P' hnone, hqsplit]
  simp only [bitWord_append, bitWord_cons, bitWord_nil, absRunFrom_append,
    absRunFrom_singleton]
  rw [hrunq]
  exact run_q_last qlast K' _ hK'

theorem absRun_accept_iff (w : Word) :
    (absRun w).state = St.accept ↔ w ∈ CFirst :=
  ⟨mem_CFirst_of_absRun_accept, absRun_accept_of_mem_CFirst⟩

theorem cFirst_recognizedBy : RecognizedBy CFirst :=
  ⟨2, 15, 5, prefixMachine, fun w =>
    (prefixMachine_accepts_iff_absRun w).trans (absRun_accept_iff w)⟩

end PegSeparation.Closure
