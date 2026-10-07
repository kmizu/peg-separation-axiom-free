import Mathlib


namespace PegSeparation.RealTimeTM

inductive Move where
  | left
  | stay
  | right
  deriving DecidableEq, Fintype, Repr

structure TapeAction (symbolCount : ℕ) where
  write : Fin symbolCount
  move : Move

structure Instruction (tapeCount stateCount symbolCount : ℕ) where
  nextState : Fin stateCount
  tapeAction : Fin tapeCount → TapeAction symbolCount

structure TapeConfiguration (symbolCount : ℕ) where
  left : List (Fin symbolCount)
  focus : Fin symbolCount
  right : List (Fin symbolCount)
  deriving DecidableEq

namespace TapeConfiguration

def popD {symbolCount : ℕ} (blank : Fin symbolCount) :
    List (Fin symbolCount) → Fin symbolCount × List (Fin symbolCount)
  | [] => (blank, [])
  | symbol :: rest => (symbol, rest)

@[simp] theorem popD_snd {symbolCount : ℕ} (blank : Fin symbolCount)
    (contents : List (Fin symbolCount)) :
    (popD blank contents).2 = contents.tail := by
  cases contents <;> rfl

def applyAction {symbolCount : ℕ} (blank : Fin symbolCount)
    (tape : TapeConfiguration symbolCount) (action : TapeAction symbolCount) :
    TapeConfiguration symbolCount :=
  match action.move with
  | .stay =>
      { tape with focus := action.write }
  | .right =>
      let popped := popD blank tape.right
      { left := action.write :: tape.left
        focus := popped.1
        right := popped.2 }
  | .left =>
      match tape.left with
      | [] =>
          { left := []
            focus := action.write
            right := tape.right }
      | next :: rest =>
          { left := rest
            focus := next
            right := action.write :: tape.right }

@[simp] theorem applyAction_stay {symbolCount : ℕ} (blank : Fin symbolCount)
    (tape : TapeConfiguration symbolCount) (write : Fin symbolCount) :
    tape.applyAction blank { write := write, move := .stay } =
      { tape with focus := write } :=
  rfl

@[simp] theorem applyAction_right_nil {symbolCount : ℕ}
    (blank : Fin symbolCount) (left : List (Fin symbolCount))
    (focus write : Fin symbolCount) :
    (TapeConfiguration.mk left focus []).applyAction blank
        { write := write, move := .right } =
      TapeConfiguration.mk (write :: left) blank [] :=
  rfl

@[simp] theorem applyAction_right_cons {symbolCount : ℕ}
    (blank : Fin symbolCount) (left : List (Fin symbolCount))
    (focus write next : Fin symbolCount) (right : List (Fin symbolCount)) :
    (TapeConfiguration.mk left focus (next :: right)).applyAction blank
        { write := write, move := .right } =
      TapeConfiguration.mk (write :: left) next right :=
  rfl

@[simp] theorem applyAction_left_nil {symbolCount : ℕ}
    (blank : Fin symbolCount) (focus write : Fin symbolCount)
    (right : List (Fin symbolCount)) :
    (TapeConfiguration.mk [] focus right).applyAction blank
        { write := write, move := .left } =
      TapeConfiguration.mk [] write right :=
  rfl

@[simp] theorem applyAction_left_cons {symbolCount : ℕ}
    (blank : Fin symbolCount) (next : Fin symbolCount)
    (left : List (Fin symbolCount)) (focus write : Fin symbolCount)
    (right : List (Fin symbolCount)) :
    (TapeConfiguration.mk (next :: left) focus right).applyAction blank
        { write := write, move := .left } =
      TapeConfiguration.mk left next (write :: right) :=
  rfl

end TapeConfiguration

structure Configuration (tapeCount stateCount symbolCount : ℕ) where
  state : Fin stateCount
  tape : Fin tapeCount → TapeConfiguration symbolCount

structure Machine (Terminal : Type) (tapeCount stateCount symbolCount : ℕ) where
  tapeCount_pos : 0 < tapeCount
  blank : Fin symbolCount
  initialState : Fin stateCount
  accepting : Finset (Fin stateCount)
  transition :
    Fin stateCount → Terminal → (Fin tapeCount → Fin symbolCount) →
      Instruction tapeCount stateCount symbolCount

namespace Machine

variable {Terminal : Type} {tapeCount stateCount symbolCount : ℕ}

def initialConfiguration
    (machine : Machine Terminal tapeCount stateCount symbolCount) :
    Configuration tapeCount stateCount symbolCount where
  state := machine.initialState
  tape := fun _ =>
    { left := []
      focus := machine.blank
      right := [] }

def step (machine : Machine Terminal tapeCount stateCount symbolCount)
    (configuration : Configuration tapeCount stateCount symbolCount)
    (terminal : Terminal) : Configuration tapeCount stateCount symbolCount :=
  let instruction := machine.transition configuration.state terminal
    (fun tape => (configuration.tape tape).focus)
  { state := instruction.nextState
    tape := fun tape =>
      (configuration.tape tape).applyAction machine.blank
        (instruction.tapeAction tape) }

def run (machine : Machine Terminal tapeCount stateCount symbolCount)
    (input : List Terminal) : Configuration tapeCount stateCount symbolCount :=
  input.foldl machine.step machine.initialConfiguration

def Accepts (machine : Machine Terminal tapeCount stateCount symbolCount)
    (input : List Terminal) : Prop :=
  (machine.run input).state ∈ machine.accepting

@[simp] theorem run_nil
    (machine : Machine Terminal tapeCount stateCount symbolCount) :
    machine.run [] = machine.initialConfiguration :=
  rfl

@[simp] theorem run_append_singleton
    (machine : Machine Terminal tapeCount stateCount symbolCount)
    (input : List Terminal) (terminal : Terminal) :
    machine.run (input ++ [terminal]) =
      machine.step (machine.run input) terminal := by
  simp [run, List.foldl_append]

end Machine

def RecognizedBy {Terminal : Type} (language : Language Terminal) : Prop :=
  ∃ (tapeCount stateCount symbolCount : ℕ)
    (machine : Machine Terminal tapeCount stateCount symbolCount),
      ∀ input, machine.Accepts input ↔ input ∈ language

end PegSeparation.RealTimeTM
