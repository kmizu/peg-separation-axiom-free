import PegSeparation.Common.Compiler.SCAToPEG.Support


namespace PegSeparation.SCAToPEG

open PegSeparation
open PegSeparation.Scaffolding

section History

variable {Terminal : Type}
variable {stateCount workLabelCount degree radius : Nat}

def reverseConfig
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) :
    Fin stateCount × Scaffold (Fin workLabelCount) degree :=
  automaton.run input.reverse

@[simp] theorem reverseConfig_nil
    (automaton : Automaton Terminal stateCount workLabelCount degree radius) :
    reverseConfig automaton [] =
      (automaton.initialState, Automaton.initialScaffold) :=
  rfl

@[simp] theorem reverseConfig_cons
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (symbol : Terminal) (input : List Terminal) :
    reverseConfig automaton (symbol :: input) =
      automaton.step (reverseConfig automaton input) symbol := by
  simp [reverseConfig, Automaton.run]

@[simp] theorem reverseConfig_nodes_cons
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (symbol : Terminal) (input : List Terminal) :
    (reverseConfig automaton (symbol :: input)).2.nodes =
      (reverseConfig automaton (symbol :: input)).2.top ::
        (reverseConfig automaton input).2.nodes := by
  rw [reverseConfig_cons]
  simp [Automaton.step, Automaton.extendScaffold, Scaffold.nodes]

@[simp] theorem reverseConfig_scaffold_nodes_length
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) :
    (reverseConfig automaton input).2.nodes.length = input.length + 1 := by
  induction input with
  | nil =>
      simp [Automaton.initialScaffold, Scaffold.nodes]
  | cons symbol input ih =>
      rw [reverseConfig_nodes_cons]
      simp [ih]

theorem reverseConfig_nodes_drop
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) (position : Nat)
    (withinInput : position ≤ input.length) :
    (reverseConfig automaton input).2.nodes.drop position =
      (reverseConfig automaton (input.drop position)).2.nodes := by
  induction input generalizing position with
  | nil =>
      have positionEq : position = 0 := Nat.eq_zero_of_le_zero (by
        simpa using withinInput)
      subst position
      rfl
  | cons symbol input ih =>
      cases position with
      | zero => rfl
      | succ position =>
          have withinTail : position ≤ input.length := by
            exact Nat.le_of_succ_le_succ (by
              simpa only [List.length_cons] using withinInput)
          rw [reverseConfig_nodes_cons]
          simpa using ih position withinTail

namespace ScaffoldLemmas

theorem follow_drop_shift {WorkLabel : Type} {degree : Nat}
    (nodes : List (Node WorkLabel degree)) (dropped relative : Nat)
    (directions : List (Fin degree)) :
    Scaffold.follow nodes (dropped + relative) directions =
      (Scaffold.follow (nodes.drop dropped) relative directions).map
        (fun endpoint => dropped + endpoint) := by
  induction directions generalizing relative with
  | nil =>
      simp [Scaffold.follow, List.getElem?_drop, Option.map_map,
        Function.comp_def]
  | cons direction directions ih =>
      simp [Scaffold.follow, List.getElem?_drop, ih, Nat.add_assoc]

theorem follow_drop {WorkLabel : Type} {degree : Nat}
    (nodes : List (Node WorkLabel degree)) (position : Nat)
    (directions : List (Fin degree)) :
    Scaffold.follow nodes position directions =
      (Scaffold.follow (nodes.drop position) 0 directions).map
        (fun endpoint => position + endpoint) := by
  simpa using follow_drop_shift nodes position 0 directions

end ScaffoldLemmas

theorem reverseConfig_follow_shift
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) (position : Nat)
    (withinInput : position ≤ input.length)
    (directions : List (Fin degree)) :
    Scaffold.follow (reverseConfig automaton input).2.nodes position directions =
      (Scaffold.follow
        (reverseConfig automaton (input.drop position)).2.nodes 0 directions).map
          (fun endpoint => position + endpoint) := by
  rw [ScaffoldLemmas.follow_drop]
  rw [reverseConfig_nodes_drop automaton input position withinInput]

theorem reverseConfig_nodes_getElem?
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) (position : Nat)
    (withinInput : position ≤ input.length) :
    (reverseConfig automaton input).2.nodes[position]? =
      some (reverseConfig automaton (input.drop position)).2.top := by
  have dropped := reverseConfig_nodes_drop automaton input position withinInput
  have heads := congrArg (fun nodes => nodes[0]?) dropped
  simpa [Scaffold.nodes, List.getElem?_drop] using heads

theorem reverseConfig_endpoint_label
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) (directions : List (Fin degree)) (position : Nat)
    (followed :
      Scaffold.follow (reverseConfig automaton input).2.nodes 0 directions =
        some position) :
    (reverseConfig automaton input).2.nodes[position]?.map Node.label =
      some (reverseConfig automaton (input.drop position)).2.top.label := by
  have positionLt :
      position < (reverseConfig automaton input).2.nodes.length :=
    ScaffoldLemmas.follow_result_lt_length followed
  have withinInput : position ≤ input.length := by
    simpa [reverseConfig_scaffold_nodes_length automaton input] using positionLt
  rw [reverseConfig_nodes_getElem? automaton input position withinInput]
  rfl

end History

end PegSeparation.SCAToPEG
