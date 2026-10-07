import PegSeparation.Common.Compiler.RealTimeTM.ToSCA


namespace PegSeparation.RealTimeTM

open PegSeparation.Scaffolding

variable {Terminal : Type}
variable {tapeCount stateCount symbolCount : ℕ}

noncomputable def nodeSlot
    (node : Node (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount))
    (tape : Fin tapeCount) : Option (Fin symbolCount) :=
  slotSymbol node.label tape

noncomputable def RepresentsChain
    (nodes : List (Node (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount)))
    (tape : Fin tapeCount) (start : Option ℕ) :
    List (Fin symbolCount) → Prop
  | [] => start = none
  | symbol :: rest =>
      ∃ position node,
        start = some position ∧
        nodes[position]? = some node ∧
        nodeSlot node tape = some symbol ∧
        RepresentsChain nodes tape
          ((node.edgeOffset (encodePort (.tail tape))).map
            (position + ·)) rest

noncomputable def RepresentsStack
    (scaffold : Scaffold (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount))
    (handle : Port tapeCount) (tape : Fin tapeCount)
    (contents : List (Fin symbolCount)) : Prop :=
  RepresentsChain scaffold.nodes tape
    (scaffold.top.edgeOffset (encodePort handle)) contents

noncomputable def Represents
    (_machine : Machine Terminal tapeCount stateCount symbolCount)
    (source : Configuration tapeCount stateCount symbolCount)
    (target :
      Fin (CompiledStateCount tapeCount stateCount symbolCount) ×
        Scaffold (Fin (CompiledLabelCount tapeCount symbolCount))
          (CompiledDegree tapeCount)) : Prop :=
  target.1 = encodeControl
      (source.state, fun tape => (source.tape tape).focus) ∧
    ∀ tape,
      RepresentsStack target.2 (.left tape) tape (source.tape tape).left ∧
      RepresentsStack target.2 (.right tape) tape (source.tape tape).right


@[simp] theorem representsChain_nil_iff
    (nodes : List (Node (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount)))
    (tape : Fin tapeCount) (start : Option ℕ) :
    RepresentsChain nodes tape start [] ↔ start = none :=
  Iff.rfl

theorem representsChain_cons_iff
    (nodes : List (Node (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount)))
    (tape : Fin tapeCount) (start : Option ℕ)
    (symbol : Fin symbolCount) (rest : List (Fin symbolCount)) :
    RepresentsChain nodes tape start (symbol :: rest) ↔
      ∃ position node,
        start = some position ∧
        nodes[position]? = some node ∧
        nodeSlot node tape = some symbol ∧
        RepresentsChain nodes tape
          ((node.edgeOffset (encodePort (.tail tape))).map
            (position + ·)) rest :=
  Iff.rfl

theorem representsChain_prepend_shift
    (fresh : Node (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount))
    (nodes : List (Node (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount)))
    (tape : Fin tapeCount) (start : Option ℕ)
    (contents : List (Fin symbolCount)) :
    RepresentsChain (fresh :: nodes) tape (start.map Nat.succ) contents ↔
      RepresentsChain nodes tape start contents := by
  induction contents generalizing start with
  | nil =>
      cases start <;> simp [RepresentsChain]
  | cons symbol rest ih =>
      cases start with
      | none => simp [RepresentsChain]
      | some position =>
          simp only [Option.map_some, RepresentsChain]
          constructor
          · rintro ⟨shifted, node, hshifted, hnode, hslot, htail⟩
            have hposition : shifted = position + 1 := by
              simpa using hshifted.symm
            subst shifted
            have hnodeOld : nodes[position]? = some node := by
              simpa using hnode
            refine ⟨position, node, rfl, hnodeOld, hslot, ?_⟩
            rw [← ih]
            convert htail using 1
            all_goals
              simp [Function.comp_def, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm]
          · rintro ⟨oldPosition, node, hposition, hnode, hslot, htail⟩
            have holdPosition : oldPosition = position := by
              exact Option.some.inj hposition.symm
            subst oldPosition
            refine ⟨position + 1, node, rfl, ?_, hslot, ?_⟩
            · simpa using hnode
            · have hshift :
                  (node.edgeOffset (encodePort (.tail tape))).map
                      (position + 1 + ·) =
                    ((node.edgeOffset (encodePort (.tail tape))).map
                      (position + ·)).map Nat.succ := by
                cases node.edgeOffset (encodePort (.tail tape)) <;>
                  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              rw [hshift]
              exact (ih _).mpr htail


theorem observedTop_eq_popD_fst
    (blank : Fin symbolCount)
    (scaffold : Scaffold (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount))
    (handle : Port tapeCount) (tape : Fin tapeCount)
    (contents : List (Fin symbolCount))
    (represented : RepresentsStack scaffold handle tape contents) :
    observedTop blank (scaffold.topNeighborhood 2) handle tape =
      (TapeConfiguration.popD blank contents).1 := by
  cases contents with
  | nil =>
      have hmissing : scaffold.top.edgeOffset (encodePort handle) = none := by
        simpa [RepresentsStack, RepresentsChain] using represented
      simp [observedTop, Scaffold.topNeighborhood, hmissing,
        TapeConfiguration.popD]
  | cons symbol rest =>
      obtain ⟨position, node, hstart, hnode, hslot, htail⟩ := represented
      have hslot' : slotSymbol node.label tape = some symbol := by
        simpa [nodeSlot] using hslot
      simp [observedTop, Scaffold.topNeighborhood, hstart,
        Scaffold.neighborhoodAt, hnode, hslot',
        TapeConfiguration.popD]

theorem atLeftBoundary_eq_isEmpty
    (scaffold : Scaffold (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount))
    (tape : Fin tapeCount) (contents : List (Fin symbolCount))
    (represented : RepresentsStack scaffold (.left tape) tape contents) :
    atLeftBoundary (scaffold.topNeighborhood 2) tape = contents.isEmpty := by
  cases contents with
  | nil =>
      have hmissing :
          scaffold.top.edgeOffset (encodePort (.left tape)) = none := by
        simpa [RepresentsStack, RepresentsChain] using represented
      simp [atLeftBoundary, Scaffold.topNeighborhood, hmissing]
  | cons symbol rest =>
      obtain ⟨position, node, hstart, hnode, hslot, htail⟩ := represented
      simp [atLeftBoundary, Scaffold.topNeighborhood, hstart,
        Scaffold.neighborhoodAt, hnode]


theorem representsChain_validate_start
    (nodes : List (Node (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount)))
    (tape : Fin tapeCount) (start : Option ℕ)
    (contents : List (Fin symbolCount))
    (represented : RepresentsChain nodes tape start contents) :
    start.bind (fun position => Scaffold.follow nodes position []) = start := by
  cases contents with
  | nil =>
      have hmissing : start = none := represented
      simp [hmissing]
  | cons symbol rest =>
      obtain ⟨position, node, hstart, hnode, hslot, htail⟩ := represented
      simp [hstart, Scaffold.follow, hnode]

theorem follow_root_handle_eq
    (scaffold : Scaffold (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount))
    (handle : Port tapeCount) (tape : Fin tapeCount)
    (contents : List (Fin symbolCount))
    (represented : RepresentsStack scaffold handle tape contents) :
    Scaffold.follow scaffold.nodes 0 [encodePort handle] =
      scaffold.top.edgeOffset (encodePort handle) := by
  have validated := representsChain_validate_start scaffold.nodes tape
    (scaffold.top.edgeOffset (encodePort handle)) contents represented
  simpa [Scaffold.follow, Scaffold.nodes, Option.bind_assoc] using validated

theorem follow_root_pop_represents_tail
    (scaffold : Scaffold (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount))
    (handle : Port tapeCount) (tape : Fin tapeCount)
    (contents : List (Fin symbolCount))
    (represented : RepresentsStack scaffold handle tape contents) :
    RepresentsChain scaffold.nodes tape
      (Scaffold.follow scaffold.nodes 0
        [encodePort handle, encodePort (.tail tape)])
      contents.tail := by
  cases contents with
  | nil =>
      have hmissing : scaffold.top.edgeOffset (encodePort handle) = none := by
        simpa [RepresentsStack, RepresentsChain] using represented
      simp [Scaffold.follow, Scaffold.nodes, hmissing]
  | cons symbol rest =>
      obtain ⟨position, node, hstart, hnode, hslot, htail⟩ := represented
      have validated := representsChain_validate_start scaffold.nodes tape
        ((node.edgeOffset (encodePort (.tail tape))).map (position + ·))
        rest htail
      have hnode' : (scaffold.top :: scaffold.older)[position]? = some node := by
        simpa [Scaffold.nodes] using hnode
      have hfollow :
          Scaffold.follow scaffold.nodes 0
              [encodePort handle, encodePort (.tail tape)] =
            (node.edgeOffset (encodePort (.tail tape))).map
              (position + ·) := by
        cases hedge : node.edgeOffset (encodePort (.tail tape)) with
        | none =>
            simp [Scaffold.follow, Scaffold.nodes, hstart, hnode', hedge]
        | some offset =>
            simpa [Scaffold.follow, Scaffold.nodes, hstart, hnode', hedge]
              using validated
      rw [hfollow]
      exact htail


theorem representsStack_extend_carry
    {actionStateCount : ℕ}
    (old : Scaffold (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount))
    (action : Action (Fin actionStateCount)
      (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount) 2)
    (oldHandle newHandle : Port tapeCount) (tape : Fin tapeCount)
    (contents : List (Fin symbolCount))
    (represented : RepresentsStack old oldHandle tape contents)
    (target : action.target (encodePort newHandle) =
      carryTarget oldHandle) :
    RepresentsStack (Automaton.extendScaffold old action)
      newHandle tape contents := by
  have hfollow := follow_root_handle_eq old oldHandle tape contents represented
  have hfollow' :
      Scaffold.follow (old.top :: old.older) 0 [encodePort oldHandle] =
        old.top.edgeOffset (encodePort oldHandle) := by
    simpa [Scaffold.nodes] using hfollow
  have shifted :=
    (representsChain_prepend_shift
      (Automaton.extendScaffold old action).top old.nodes tape
      (old.top.edgeOffset (encodePort oldHandle)) contents).mpr represented
  simpa [RepresentsStack, Automaton.extendScaffold, Scaffold.nodes,
    target, carryTarget, hfollow'] using shifted

theorem representsStack_extend_pop
    {actionStateCount : ℕ}
    (old : Scaffold (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount))
    (action : Action (Fin actionStateCount)
      (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount) 2)
    (oldHandle newHandle : Port tapeCount) (tape : Fin tapeCount)
    (contents : List (Fin symbolCount))
    (represented : RepresentsStack old oldHandle tape contents)
    (target : action.target (encodePort newHandle) =
      popTarget oldHandle tape) :
    RepresentsStack (Automaton.extendScaffold old action)
      newHandle tape contents.tail := by
  have tailRep := follow_root_pop_represents_tail old oldHandle tape contents represented
  have shifted :=
    (representsChain_prepend_shift
      (Automaton.extendScaffold old action).top old.nodes tape
      (Scaffold.follow old.nodes 0
        [encodePort oldHandle, encodePort (.tail tape)])
      contents.tail).mpr tailRep
  simpa [RepresentsStack, Automaton.extendScaffold, Scaffold.nodes,
    target, popTarget] using shifted

theorem representsStack_extend_push
    {actionStateCount : ℕ}
    (old : Scaffold (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount))
    (action : Action (Fin actionStateCount)
      (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount) 2)
    (oldHandle newHandle : Port tapeCount) (tape : Fin tapeCount)
    (symbol : Fin symbolCount) (contents : List (Fin symbolCount))
    (represented : RepresentsStack old oldHandle tape contents)
    (handleTarget : action.target (encodePort newHandle) = .self)
    (tailTarget : action.target (encodePort (.tail tape)) =
      carryTarget oldHandle)
    (labelSlot : decodeLabel action.newLabel tape = some symbol) :
    RepresentsStack (Automaton.extendScaffold old action)
      newHandle tape (symbol :: contents) := by
  have hfollow := follow_root_handle_eq old oldHandle tape contents represented
  have hfollow' :
      Scaffold.follow (old.top :: old.older) 0 [encodePort oldHandle] =
        old.top.edgeOffset (encodePort oldHandle) := by
    simpa [Scaffold.nodes] using hfollow
  have shifted :=
    (representsChain_prepend_shift
      (Automaton.extendScaffold old action).top old.nodes tape
      (old.top.edgeOffset (encodePort oldHandle)) contents).mpr represented
  rw [RepresentsStack, representsChain_cons_iff]
  refine ⟨0, (Automaton.extendScaffold old action).top, ?_, ?_, ?_, ?_⟩
  · simp [Automaton.extendScaffold, handleTarget]
  · simp [Scaffold.nodes]
  · simpa [Automaton.extendScaffold, nodeSlot, slotSymbol] using labelSlot
  · simpa [Automaton.extendScaffold, Scaffold.nodes, tailTarget,
      carryTarget, hfollow', Function.comp_def, Nat.succ_eq_add_one] using shifted


theorem instructionFocus_eq_applyAction_focus
    (machine : Machine Terminal tapeCount stateCount symbolCount)
    (source : Configuration tapeCount stateCount symbolCount)
    (scaffold : Scaffold (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount))
    (instruction : Instruction tapeCount stateCount symbolCount)
    (stackRep : ∀ tape,
      RepresentsStack scaffold (.left tape) tape (source.tape tape).left ∧
      RepresentsStack scaffold (.right tape) tape (source.tape tape).right) :
    instructionFocus machine.blank (scaffold.topNeighborhood 2) instruction =
      fun tape =>
        ((source.tape tape).applyAction machine.blank
          (instruction.tapeAction tape)).focus := by
  funext tape
  have hleft := observedTop_eq_popD_fst machine.blank scaffold
    (.left tape) tape (source.tape tape).left (stackRep tape).1
  have hright := observedTop_eq_popD_fst machine.blank scaffold
    (.right tape) tape (source.tape tape).right (stackRep tape).2
  rcases haction : instruction.tapeAction tape with ⟨write, move⟩
  cases move with
  | stay =>
      simp [instructionFocus, haction, TapeConfiguration.applyAction]
  | right =>
      simpa [instructionFocus, haction, TapeConfiguration.applyAction] using hright
  | left =>
      have hboundary := atLeftBoundary_eq_isEmpty scaffold tape
        (source.tape tape).left (stackRep tape).1
      cases hcontents : (source.tape tape).left with
      | nil =>
          simp [hcontents] at hboundary
          simp [instructionFocus, haction, TapeConfiguration.applyAction,
            hcontents, hboundary]
      | cons next rest =>
          simp [hcontents] at hboundary
          simpa [instructionFocus, haction, TapeConfiguration.applyAction,
            TapeConfiguration.popD, hcontents, hboundary] using hleft

theorem instructionSCAAction_preserves_stacks
    (machine : Machine Terminal tapeCount stateCount symbolCount)
    (source : Configuration tapeCount stateCount symbolCount)
    (scaffold : Scaffold (Fin (CompiledLabelCount tapeCount symbolCount))
      (CompiledDegree tapeCount))
    (instruction : Instruction tapeCount stateCount symbolCount)
    (stackRep : ∀ tape,
      RepresentsStack scaffold (.left tape) tape (source.tape tape).left ∧
      RepresentsStack scaffold (.right tape) tape (source.tape tape).right) :
    let action := instructionSCAAction machine.blank
      (scaffold.topNeighborhood 2) instruction
    ∀ tape,
      RepresentsStack (Automaton.extendScaffold scaffold action)
          (.left tape) tape
          ((source.tape tape).applyAction machine.blank
            (instruction.tapeAction tape)).left ∧
        RepresentsStack (Automaton.extendScaffold scaffold action)
          (.right tape) tape
          ((source.tape tape).applyAction machine.blank
            (instruction.tapeAction tape)).right := by
  dsimp only
  intro tape
  let action := instructionSCAAction machine.blank
    (scaffold.topNeighborhood 2) instruction
  rcases haction : instruction.tapeAction tape with ⟨write, move⟩
  cases move with
  | stay =>
      constructor
      · simpa [TapeConfiguration.applyAction, haction] using
          representsStack_extend_carry scaffold action (.left tape) (.left tape)
            tape (source.tape tape).left (stackRep tape).1 (by
              simp [action, instructionSCAAction, instructionTarget, haction])
      · simpa [TapeConfiguration.applyAction, haction] using
          representsStack_extend_carry scaffold action (.right tape) (.right tape)
            tape (source.tape tape).right (stackRep tape).2 (by
              simp [action, instructionSCAAction, instructionTarget, haction])
  | right =>
      constructor
      · simpa [TapeConfiguration.applyAction, haction] using
          representsStack_extend_push scaffold action (.left tape) (.left tape)
            tape write (source.tape tape).left (stackRep tape).1 (by
              simp [action, instructionSCAAction, instructionTarget, haction]) (by
              simp [action, instructionSCAAction, instructionTarget, haction]) (by
              simp [action, instructionSCAAction, instructionLabel, haction])
      · simpa [TapeConfiguration.applyAction, haction] using
          representsStack_extend_pop scaffold action (.right tape) (.right tape)
            tape (source.tape tape).right (stackRep tape).2 (by
              simp [action, instructionSCAAction, instructionTarget, haction])
  | left =>
      have hboundary := atLeftBoundary_eq_isEmpty scaffold tape
        (source.tape tape).left (stackRep tape).1
      cases hcontents : (source.tape tape).left with
      | nil =>
          simp [hcontents] at hboundary
          constructor
          · simpa [TapeConfiguration.applyAction, haction, hcontents] using
              representsStack_extend_carry scaffold action
                (.left tape) (.left tape) tape (source.tape tape).left
                (stackRep tape).1 (by
                  simp [action, instructionSCAAction, instructionTarget,
                    haction, hboundary])
          · simpa [TapeConfiguration.applyAction, haction, hcontents] using
              representsStack_extend_carry scaffold action
                (.right tape) (.right tape) tape (source.tape tape).right
                (stackRep tape).2 (by
                  simp [action, instructionSCAAction, instructionTarget,
                    haction, hboundary])
      | cons next rest =>
          simp [hcontents] at hboundary
          constructor
          · simpa [TapeConfiguration.applyAction, haction, hcontents] using
              representsStack_extend_pop scaffold action
                (.left tape) (.left tape) tape (source.tape tape).left
                (stackRep tape).1 (by
                  simp [action, instructionSCAAction, instructionTarget,
                    haction, hboundary])
          · simpa [TapeConfiguration.applyAction, haction, hcontents] using
              representsStack_extend_push scaffold action
                (.right tape) (.right tape) tape write
                (source.tape tape).right (stackRep tape).2 (by
                  simp [action, instructionSCAAction, instructionTarget,
                    haction, hboundary]) (by
                  simp [action, instructionSCAAction, instructionTarget,
                    haction, hboundary]) (by
                  simp [action, instructionSCAAction, instructionLabel,
                    haction, hboundary])

theorem step_preserves_representation
    (machine : Machine Terminal tapeCount stateCount symbolCount)
    (source : Configuration tapeCount stateCount symbolCount)
    (target :
      Fin (CompiledStateCount tapeCount stateCount symbolCount) ×
        Scaffold (Fin (CompiledLabelCount tapeCount symbolCount))
          (CompiledDegree tapeCount))
    (terminal : Terminal)
    (represented : Represents machine source target) :
    Represents machine (machine.step source terminal)
      ((toSCA machine).step target terminal) := by
  rcases target with ⟨targetState, scaffold⟩
  rcases represented with ⟨hstate, stackRep⟩
  change targetState =
    encodeControl (source.state, fun tape => (source.tape tape).focus) at hstate
  subst targetState
  let instruction := machine.transition source.state terminal
    (fun tape => (source.tape tape).focus)
  let action := instructionSCAAction machine.blank
    (scaffold.topNeighborhood 2) instruction
  have htargetStep :
      (toSCA machine).step
          (encodeControl
            (source.state, fun tape => (source.tape tape).focus), scaffold)
          terminal =
        (action.nextState, Automaton.extendScaffold scaffold action) := by
    simp [Automaton.step, toSCA, compiledAction, action, instruction]
  rw [htargetStep]
  constructor
  · have hfocus := instructionFocus_eq_applyAction_focus
        machine source scaffold instruction stackRep
    simpa [Machine.step, instruction, action, instructionSCAAction] using
      congrArg (fun focus => encodeControl (instruction.nextState, focus)) hfocus
  · have preserved := instructionSCAAction_preserves_stacks
        machine source scaffold instruction stackRep
    simpa [Machine.step, instruction, action] using preserved


theorem initial_representation
    (machine : Machine Terminal tapeCount stateCount symbolCount) :
    Represents machine machine.initialConfiguration
      ((toSCA machine).initialState, Automaton.initialScaffold) := by
  constructor
  · simp [Machine.initialConfiguration, toSCA]
  · intro tape
    constructor <;>
      simp [RepresentsStack, Automaton.initialScaffold,
        Machine.initialConfiguration]

theorem foldl_preserves_representation
    (machine : Machine Terminal tapeCount stateCount symbolCount)
    (input : List Terminal)
    (source : Configuration tapeCount stateCount symbolCount)
    (target :
      Fin (CompiledStateCount tapeCount stateCount symbolCount) ×
        Scaffold (Fin (CompiledLabelCount tapeCount symbolCount))
          (CompiledDegree tapeCount))
    (represented : Represents machine source target) :
    Represents machine (input.foldl machine.step source)
      (input.foldl (toSCA machine).step target) := by
  induction input generalizing source target with
  | nil => exact represented
  | cons terminal rest ih =>
      exact ih (machine.step source terminal)
        ((toSCA machine).step target terminal)
        (step_preserves_representation machine source target terminal represented)

theorem run_represents
    (machine : Machine Terminal tapeCount stateCount symbolCount)
    (input : List Terminal) :
    Represents machine (machine.run input) ((toSCA machine).run input) := by
  exact foldl_preserves_representation machine input
    machine.initialConfiguration
    ((toSCA machine).initialState, Automaton.initialScaffold)
    (initial_representation machine)

theorem toSCA_accepts_iff
    (machine : Machine Terminal tapeCount stateCount symbolCount)
    (input : List Terminal) :
    (toSCA machine).Accepts input ↔ machine.Accepts input := by
  have represented := run_represents machine input
  have hstate := represented.1
  simp only [Automaton.Accepts, Machine.Accepts]
  rw [hstate]
  simp [toSCA]

theorem recognizedBySCA_of_recognizedBy
    {language : Language Terminal} (recognized : RecognizedBy language) :
    ∃ (scaStateCount scaLabelCount degree radius : ℕ)
      (automaton : Automaton Terminal
        scaStateCount scaLabelCount degree radius),
      ∀ input, automaton.Accepts input ↔ input ∈ language := by
  obtain ⟨sourceTapeCount, sourceStateCount, sourceSymbolCount,
    machine, hmachine⟩ := recognized
  refine ⟨CompiledStateCount sourceTapeCount sourceStateCount sourceSymbolCount,
    CompiledLabelCount sourceTapeCount sourceSymbolCount,
    CompiledDegree sourceTapeCount, 2, toSCA machine, ?_⟩
  intro input
  exact (toSCA_accepts_iff machine input).trans (hmachine input)

end PegSeparation.RealTimeTM
