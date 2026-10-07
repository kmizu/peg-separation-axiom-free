import PegSeparation.Common.Compiler.RealTimeTM.Model
import PegSeparation.Common.Model.Scaffolding


namespace PegSeparation.RealTimeTM

open PegSeparation.Scaffolding

inductive Port (tapeCount : ℕ) where
  | left (tape : Fin tapeCount)
  | right (tape : Fin tapeCount)
  | tail (tape : Fin tapeCount)
  deriving DecidableEq, Fintype, Repr

abbrev CompiledControl (tapeCount stateCount symbolCount : ℕ) :=
  Fin stateCount × (Fin tapeCount → Fin symbolCount)

abbrev CompiledLabel (tapeCount symbolCount : ℕ) :=
  Fin tapeCount → Option (Fin symbolCount)

abbrev CompiledStateCount (tapeCount stateCount symbolCount : ℕ) :=
  Fintype.card (CompiledControl tapeCount stateCount symbolCount)

abbrev CompiledLabelCount (tapeCount symbolCount : ℕ) :=
  Fintype.card (CompiledLabel tapeCount symbolCount)

abbrev CompiledDegree (tapeCount : ℕ) :=
  Fintype.card (Port tapeCount)


noncomputable def controlEquiv (tapeCount stateCount symbolCount : ℕ) :
    CompiledControl tapeCount stateCount symbolCount ≃
      Fin (CompiledStateCount tapeCount stateCount symbolCount) :=
  Fintype.equivFin _

noncomputable def labelEquiv (tapeCount symbolCount : ℕ) :
    CompiledLabel tapeCount symbolCount ≃
      Fin (CompiledLabelCount tapeCount symbolCount) :=
  Fintype.equivFin _

noncomputable def portEquiv (tapeCount : ℕ) :
    Port tapeCount ≃ Fin (CompiledDegree tapeCount) :=
  Fintype.equivFin _

noncomputable def encodeControl
    {tapeCount stateCount symbolCount : ℕ}
    (control : CompiledControl tapeCount stateCount symbolCount) :
    Fin (CompiledStateCount tapeCount stateCount symbolCount) :=
  controlEquiv tapeCount stateCount symbolCount control

noncomputable def decodeControl
    {tapeCount stateCount symbolCount : ℕ}
    (code : Fin (CompiledStateCount tapeCount stateCount symbolCount)) :
    CompiledControl tapeCount stateCount symbolCount :=
  (controlEquiv tapeCount stateCount symbolCount).symm code

noncomputable def encodeLabel {tapeCount symbolCount : ℕ}
    (label : CompiledLabel tapeCount symbolCount) :
    Fin (CompiledLabelCount tapeCount symbolCount) :=
  labelEquiv tapeCount symbolCount label

noncomputable def decodeLabel {tapeCount symbolCount : ℕ}
    (code : Fin (CompiledLabelCount tapeCount symbolCount)) :
    CompiledLabel tapeCount symbolCount :=
  (labelEquiv tapeCount symbolCount).symm code

noncomputable def encodePort {tapeCount : ℕ} (port : Port tapeCount) :
    Fin (CompiledDegree tapeCount) :=
  portEquiv tapeCount port

noncomputable def decodePort {tapeCount : ℕ}
    (code : Fin (CompiledDegree tapeCount)) : Port tapeCount :=
  (portEquiv tapeCount).symm code

@[simp] theorem decode_encode_control
    {tapeCount stateCount symbolCount : ℕ}
    (control : CompiledControl tapeCount stateCount symbolCount) :
    decodeControl (encodeControl control) = control :=
  (controlEquiv tapeCount stateCount symbolCount).symm_apply_apply control

@[simp] theorem encode_decode_control
    {tapeCount stateCount symbolCount : ℕ}
    (code : Fin (CompiledStateCount tapeCount stateCount symbolCount)) :
    encodeControl (decodeControl code) = code :=
  (controlEquiv tapeCount stateCount symbolCount).apply_symm_apply code

@[simp] theorem decode_encode_label {tapeCount symbolCount : ℕ}
    (label : CompiledLabel tapeCount symbolCount) :
    decodeLabel (encodeLabel label) = label :=
  (labelEquiv tapeCount symbolCount).symm_apply_apply label

@[simp] theorem encode_decode_label {tapeCount symbolCount : ℕ}
    (code : Fin (CompiledLabelCount tapeCount symbolCount)) :
    encodeLabel (decodeLabel code) = code :=
  (labelEquiv tapeCount symbolCount).apply_symm_apply code

@[simp] theorem decode_encode_port {tapeCount : ℕ} (port : Port tapeCount) :
    decodePort (encodePort port) = port :=
  (portEquiv tapeCount).symm_apply_apply port

@[simp] theorem encode_decode_port {tapeCount : ℕ}
    (code : Fin (CompiledDegree tapeCount)) :
    encodePort (decodePort code) = code :=
  (portEquiv tapeCount).apply_symm_apply code


noncomputable def slotSymbol {tapeCount symbolCount : ℕ}
    (label : Option (Fin (CompiledLabelCount tapeCount symbolCount)))
    (tape : Fin tapeCount) : Option (Fin symbolCount) :=
  label.bind fun code => decodeLabel code tape

noncomputable def observedTop {tapeCount symbolCount : ℕ}
    (blank : Fin symbolCount)
    (view : Neighborhood (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount) 2)
    (handle : Port tapeCount) (tape : Fin tapeCount) : Fin symbolCount :=
  match view.2 (encodePort handle) with
  | none => blank
  | some endpoint => (slotSymbol endpoint.1 tape).getD blank

noncomputable def atLeftBoundary {tapeCount symbolCount : ℕ}
    (view : Neighborhood (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount) 2)
    (tape : Fin tapeCount) : Bool :=
  (view.2 (encodePort (.left tape))).isNone

noncomputable def carryTarget {tapeCount : ℕ} (port : Port tapeCount) :
    LocalTarget (CompiledDegree tapeCount) 2 :=
  .path [encodePort port] (by simp)

noncomputable def popTarget {tapeCount : ℕ}
    (handle : Port tapeCount) (tape : Fin tapeCount) :
    LocalTarget (CompiledDegree tapeCount) 2 :=
  .path [encodePort handle, encodePort (.tail tape)] (by simp)

noncomputable def instructionLabel {tapeCount stateCount symbolCount : ℕ}
    (view : Neighborhood (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount) 2)
    (instruction : Instruction tapeCount stateCount symbolCount) :
    CompiledLabel tapeCount symbolCount := fun tape =>
  let action := instruction.tapeAction tape
  match action.move with
  | .stay => none
  | .right => some action.write
  | .left =>
      if atLeftBoundary view tape then none else some action.write

noncomputable def instructionFocus {tapeCount stateCount symbolCount : ℕ}
    (blank : Fin symbolCount)
    (view : Neighborhood (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount) 2)
    (instruction : Instruction tapeCount stateCount symbolCount) :
    Fin tapeCount → Fin symbolCount := fun tape =>
  let action := instruction.tapeAction tape
  match action.move with
  | .stay => action.write
  | .right => observedTop blank view (.right tape) tape
  | .left =>
      if atLeftBoundary view tape then action.write
      else observedTop blank view (.left tape) tape

noncomputable def instructionTarget {tapeCount stateCount symbolCount : ℕ}
    (view : Neighborhood (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount) 2)
    (instruction : Instruction tapeCount stateCount symbolCount)
    (port : Fin (CompiledDegree tapeCount)) :
    LocalTarget (CompiledDegree tapeCount) 2 :=
  match decodePort port with
  | .left tape =>
      match (instruction.tapeAction tape).move with
      | .stay => carryTarget (.left tape)
      | .right => .self
      | .left =>
          if atLeftBoundary view tape then carryTarget (.left tape)
          else popTarget (.left tape) tape
  | .right tape =>
      match (instruction.tapeAction tape).move with
      | .stay => carryTarget (.right tape)
      | .right => popTarget (.right tape) tape
      | .left =>
          if atLeftBoundary view tape then carryTarget (.right tape)
          else .self
  | .tail tape =>
      match (instruction.tapeAction tape).move with
      | .stay => .missing
      | .right => carryTarget (.left tape)
      | .left =>
          if atLeftBoundary view tape then .missing
          else carryTarget (.right tape)

noncomputable def instructionSCAAction
    {tapeCount stateCount symbolCount : ℕ}
    (blank : Fin symbolCount)
    (view : Neighborhood (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount) 2)
    (instruction : Instruction tapeCount stateCount symbolCount) :
    Action
      (Fin (CompiledStateCount tapeCount stateCount symbolCount))
      (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount) 2 where
  nextState := encodeControl
    (instruction.nextState, instructionFocus blank view instruction)
  newLabel := encodeLabel (instructionLabel view instruction)
  target := instructionTarget view instruction

noncomputable def compiledAction
    {Terminal : Type} {tapeCount stateCount symbolCount : ℕ}
    (machine : Machine Terminal tapeCount stateCount symbolCount)
    (state : Fin (CompiledStateCount tapeCount stateCount symbolCount))
    (terminal : Terminal)
    (view : Neighborhood (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount) 2) :
    Action
      (Fin (CompiledStateCount tapeCount stateCount symbolCount))
      (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount) 2 :=
  let control := decodeControl state
  let instruction := machine.transition control.1 terminal control.2
  instructionSCAAction machine.blank view instruction

noncomputable def toSCA
    {Terminal : Type} {tapeCount stateCount symbolCount : ℕ}
    (machine : Machine Terminal tapeCount stateCount symbolCount) :
    Automaton Terminal
      (CompiledStateCount tapeCount stateCount symbolCount)
      (CompiledLabelCount tapeCount symbolCount)
      (CompiledDegree tapeCount) 2 where
  degreePositive := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨Port.left ⟨0, machine.tapeCount_pos⟩⟩
  initialState := encodeControl
    (machine.initialState, fun _ => machine.blank)
  accepting := Finset.univ.filter fun state =>
    (decodeControl state).1 ∈ machine.accepting
  transition := compiledAction machine

end PegSeparation.RealTimeTM
