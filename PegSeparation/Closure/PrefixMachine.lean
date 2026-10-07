import PegSeparation.Closure.Definitions
import PegSeparation.Common.Compiler.RealTimeTM.Model


namespace PegSeparation.Closure

open PegSeparation.Witness.LanguageCFG
open PegSeparation.RealTimeTM


inductive Sym where
  | blank
  | b0
  | b1
  | m0
  | m1
  deriving DecidableEq, Repr

def encBit : Bit → Sym
  | false => .b0
  | true => .b1

def encMark : Bit → Sym
  | false => .m0
  | true => .m1

def symRead : Sym → Option (Bit × Bool)
  | .blank => none
  | .b0 => some (false, false)
  | .b1 => some (true, false)
  | .m0 => some (false, true)
  | .m1 => some (true, true)


inductive St where
  | start
  | key1
  | key2
  | pay1
  | pay2
  | between
  | skipKey1
  | skipKey2
  | skipPay1
  | skipPay2
  | xEven
  | xOdd
  | qRead
  | accept
  | reject
  deriving DecidableEq, Repr


structure AbsTape where
  left : List Sym
  focus : Sym
  right : List Sym
  deriving DecidableEq

structure AbsConfig where
  state : St
  key : AbsTape
  pay : AbsTape

structure AbsInstr where
  next : St
  keyWrite : Sym
  keyMove : Move
  payWrite : Sym
  payMove : Move


def holdBoth (s : St) : AbsInstr :=
  ⟨s, .blank, .stay, .blank, .stay⟩

def rejectInstr : AbsInstr := holdBoth .reject

def pushKey (s : St) (w : Sym) : AbsInstr := ⟨s, w, .right, .blank, .stay⟩

def pushPay (s : St) (w : Sym) : AbsInstr := ⟨s, .blank, .stay, w, .right⟩

def popKey (s : St) : AbsInstr := ⟨s, .blank, .left, .blank, .stay⟩

def popPay (s : St) : AbsInstr := ⟨s, .blank, .stay, .blank, .left⟩

def transStart : Terminal → AbsInstr
  | .langle => holdBoth .key1
  | _ => rejectInstr

def transKey1 : Terminal → AbsInstr
  | .bit0 => pushKey .key2 (encMark false)
  | .bit1 => pushKey .key2 (encMark true)
  | _ => rejectInstr

def transKey2 : Terminal → AbsInstr
  | .bit0 => pushKey .key2 (encBit false)
  | .bit1 => pushKey .key2 (encBit true)
  | .colon => holdBoth .pay1
  | _ => rejectInstr

def transPay1 : Terminal → AbsInstr
  | .bit0 => pushPay .pay2 (encMark false)
  | .bit1 => pushPay .pay2 (encMark true)
  | _ => rejectInstr

def transPay2 : Terminal → AbsInstr
  | .bit0 => pushPay .pay2 (encBit false)
  | .bit1 => pushPay .pay2 (encBit true)
  | .rangle => holdBoth .between
  | _ => rejectInstr

def transBetween : Terminal → AbsInstr
  | .langle => holdBoth .skipKey1
  | .dollar => popPay .xEven
  | _ => rejectInstr

def transSkipKey1 : Terminal → AbsInstr
  | .bit0 => holdBoth .skipKey2
  | .bit1 => holdBoth .skipKey2
  | _ => rejectInstr

def transSkipKey2 : Terminal → AbsInstr
  | .bit0 => holdBoth .skipKey2
  | .bit1 => holdBoth .skipKey2
  | .colon => holdBoth .skipPay1
  | _ => rejectInstr

def transSkipPay1 : Terminal → AbsInstr
  | .bit0 => holdBoth .skipPay2
  | .bit1 => holdBoth .skipPay2
  | _ => rejectInstr

def transSkipPay2 : Terminal → AbsInstr
  | .bit0 => holdBoth .skipPay2
  | .bit1 => holdBoth .skipPay2
  | .rangle => holdBoth .between
  | _ => rejectInstr

def xStateOf : Bool → St
  | false => .xEven
  | true => .xOdd

def transXBit (parity a : Bit) (payFocus : Sym) : AbsInstr :=
  match symRead payFocus with
  | none => rejectInstr
  | some entry => popPay (xStateOf (xor parity (a && entry.1)))

def transX (parity : Bool) (payFocus : Sym) : Terminal → AbsInstr
  | .bit0 => transXBit parity false payFocus
  | .bit1 => transXBit parity true payFocus
  | .hash =>
      match parity, symRead payFocus with
      | true, none => popKey .qRead
      | _, _ => rejectInstr
  | _ => rejectInstr

def transQBit (a : Bit) (keyFocus : Sym) : AbsInstr :=
  match symRead keyFocus with
  | none => rejectInstr
  | some entry =>
      if a = entry.1 then popKey (if entry.2 then .accept else .qRead)
      else rejectInstr

def transQ (keyFocus : Sym) : Terminal → AbsInstr
  | .bit0 => transQBit false keyFocus
  | .bit1 => transQBit true keyFocus
  | _ => rejectInstr

def absTrans (s : St) (t : Terminal) (keyFocus payFocus : Sym) : AbsInstr :=
  match s with
  | .start => transStart t
  | .key1 => transKey1 t
  | .key2 => transKey2 t
  | .pay1 => transPay1 t
  | .pay2 => transPay2 t
  | .between => transBetween t
  | .skipKey1 => transSkipKey1 t
  | .skipKey2 => transSkipKey2 t
  | .skipPay1 => transSkipPay1 t
  | .skipPay2 => transSkipPay2 t
  | .xEven => transX false payFocus t
  | .xOdd => transX true payFocus t
  | .qRead => transQ keyFocus t
  | .accept => rejectInstr
  | .reject => rejectInstr


def applyAbs (tape : AbsTape) (w : Sym) (m : Move) : AbsTape :=
  match m with
  | .stay => { tape with focus := w }
  | .right =>
      match tape.right with
      | [] => ⟨w :: tape.left, .blank, []⟩
      | next :: rest => ⟨w :: tape.left, next, rest⟩
  | .left =>
      match tape.left with
      | [] => ⟨[], w, tape.right⟩
      | next :: rest => ⟨rest, next, w :: tape.right⟩

def absStep (c : AbsConfig) (t : Terminal) : AbsConfig :=
  let instruction := absTrans c.state t c.key.focus c.pay.focus
  ⟨instruction.next,
    applyAbs c.key instruction.keyWrite instruction.keyMove,
    applyAbs c.pay instruction.payWrite instruction.payMove⟩

def absInit : AbsConfig := ⟨.start, ⟨[], .blank, []⟩, ⟨[], .blank, []⟩⟩

def absRunFrom (c : AbsConfig) (w : Word) : AbsConfig := w.foldl absStep c

def absRun (w : Word) : AbsConfig := absRunFrom absInit w

@[simp] theorem absRunFrom_nil (c : AbsConfig) : absRunFrom c [] = c := rfl

@[simp] theorem absRunFrom_cons (c : AbsConfig) (t : Terminal) (w : Word) :
    absRunFrom c (t :: w) = absRunFrom (absStep c t) w := rfl

theorem absRunFrom_append (c : AbsConfig) (u v : Word) :
    absRunFrom c (u ++ v) = absRunFrom (absRunFrom c u) v := by
  simp [absRunFrom, List.foldl_append]

theorem absRunFrom_singleton (c : AbsConfig) (t : Terminal) :
    absRunFrom c [t] = absStep c t := rfl

theorem absRun_append_singleton (w : Word) (t : Terminal) :
    absRun (w ++ [t]) = absStep (absRun w) t := by
  simp [absRun, absRunFrom_append]


def symToFin : Sym → Fin 5
  | .blank => 0
  | .b0 => 1
  | .b1 => 2
  | .m0 => 3
  | .m1 => 4

def finToSym (i : Fin 5) : Sym :=
  [Sym.blank, Sym.b0, Sym.b1, Sym.m0, Sym.m1].getD i.val .blank

@[simp] theorem finToSym_symToFin (s : Sym) : finToSym (symToFin s) = s := by
  cases s <;> rfl

def stToFin : St → Fin 15
  | .start => 0
  | .key1 => 1
  | .key2 => 2
  | .pay1 => 3
  | .pay2 => 4
  | .between => 5
  | .skipKey1 => 6
  | .skipKey2 => 7
  | .skipPay1 => 8
  | .skipPay2 => 9
  | .xEven => 10
  | .xOdd => 11
  | .qRead => 12
  | .accept => 13
  | .reject => 14

def finToSt (i : Fin 15) : St :=
  [St.start, St.key1, St.key2, St.pay1, St.pay2, St.between, St.skipKey1,
    St.skipKey2, St.skipPay1, St.skipPay2, St.xEven, St.xOdd, St.qRead,
    St.accept, St.reject].getD i.val .reject

@[simp] theorem finToSt_stToFin (s : St) : finToSt (stToFin s) = s := by
  cases s <;> rfl

theorem stToFin_injective : Function.Injective stToFin :=
  Function.LeftInverse.injective finToSt_stToFin

def prefixMachine : Machine Terminal 2 15 5 where
  tapeCount_pos := by norm_num
  blank := symToFin .blank
  initialState := stToFin .start
  accepting := {stToFin .accept}
  transition := fun s t focus =>
    let instruction :=
      absTrans (finToSt s) t (finToSym (focus 0)) (finToSym (focus 1))
    { nextState := stToFin instruction.next
      tapeAction := fun j =>
        if j = 0 then ⟨symToFin instruction.keyWrite, instruction.keyMove⟩
        else ⟨symToFin instruction.payWrite, instruction.payMove⟩ }

def encTape (tape : AbsTape) : TapeConfiguration 5 :=
  ⟨tape.left.map symToFin, symToFin tape.focus, tape.right.map symToFin⟩

def encConfig (c : AbsConfig) : Configuration 2 15 5 where
  state := stToFin c.state
  tape := fun j => if j = 0 then encTape c.key else encTape c.pay

private theorem encTape_applyAbs (tape : AbsTape) (w : Sym) (m : Move) :
    encTape (applyAbs tape w m) =
      (encTape tape).applyAction (symToFin .blank) ⟨symToFin w, m⟩ := by
  obtain ⟨left, focus, right⟩ := tape
  cases m with
  | stay => rfl
  | right => cases right <;> rfl
  | left => cases left <;> rfl

@[simp] private theorem encTape_focus (tape : AbsTape) :
    (encTape tape).focus = symToFin tape.focus := rfl

private theorem config_ext {a b : Configuration 2 15 5}
    (hstate : a.state = b.state) (htape : a.tape = b.tape) : a = b := by
  obtain ⟨sa, ta⟩ := a
  obtain ⟨sb, tb⟩ := b
  simp_all

private theorem encConfig_tape_zero (c : AbsConfig) :
    (encConfig c).tape 0 = encTape c.key := by
  simp [encConfig]

private theorem encConfig_tape_one (c : AbsConfig) :
    (encConfig c).tape 1 = encTape c.pay := by
  simp [encConfig]

private theorem step_encConfig (c : AbsConfig) (t : Terminal) :
    prefixMachine.step (encConfig c) t = encConfig (absStep c t) := by
  refine config_ext ?_ ?_
  · simp [Machine.step, prefixMachine, absStep, encConfig]
  · funext j
    fin_cases j
    · simp [Machine.step, prefixMachine, absStep, encConfig, encTape_applyAbs]
    · simp [Machine.step, prefixMachine, absStep, encConfig, encTape_applyAbs]

private theorem foldl_step_encConfig (w : Word) (c : AbsConfig) :
    w.foldl prefixMachine.step (encConfig c) = encConfig (absRunFrom c w) := by
  induction w generalizing c with
  | nil => rfl
  | cons t rest ih =>
      simp only [List.foldl_cons, absRunFrom_cons]
      rw [step_encConfig, ih]

private theorem initialConfiguration_eq :
    prefixMachine.initialConfiguration = encConfig absInit := by
  refine config_ext rfl ?_
  funext j
  fin_cases j <;> simp [Machine.initialConfiguration, encConfig, encTape,
    absInit, prefixMachine]

theorem prefixMachine_run (w : Word) :
    prefixMachine.run w = encConfig (absRun w) := by
  rw [Machine.run, initialConfiguration_eq, foldl_step_encConfig]
  rfl

private theorem prefixMachine_accepting_iff (s : St) :
    stToFin s ∈ prefixMachine.accepting ↔ s = St.accept := by
  constructor
  · intro h
    exact stToFin_injective (Finset.mem_singleton.mp h)
  · rintro rfl
    exact Finset.mem_singleton_self _

theorem prefixMachine_accepts_iff_absRun (w : Word) :
    prefixMachine.Accepts w ↔ (absRun w).state = St.accept := by
  have h : (prefixMachine.run w).state = stToFin (absRun w).state := by
    rw [prefixMachine_run]
    rfl
  change (prefixMachine.run w).state ∈ prefixMachine.accepting ↔ _
  rw [h]
  exact prefixMachine_accepting_iff _

end PegSeparation.Closure
