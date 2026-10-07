import Mathlib


namespace PegSeparation

namespace Scaffolding

def Neighborhood (WorkLabel : Type) (degree : Nat) : Nat → Type
  | 0 => Option WorkLabel
  | radius + 1 =>
      Option WorkLabel × (Fin degree → Option (Neighborhood WorkLabel degree radius))

structure Node (WorkLabel : Type) (degree : Nat) where
  label : Option WorkLabel
  edgeOffset : Fin degree → Option Nat

structure Scaffold (WorkLabel : Type) (degree : Nat) where
  top : Node WorkLabel degree
  older : List (Node WorkLabel degree)

namespace Scaffold

variable {WorkLabel : Type} {degree : Nat}

def nodes (scaffold : Scaffold WorkLabel degree) : List (Node WorkLabel degree) :=
  scaffold.top :: scaffold.older

def follow (allNodes : List (Node WorkLabel degree)) :
    Nat → List (Fin degree) → Option Nat
  | position, [] => allNodes[position]?.map (fun _ => position)
  | position, direction :: directions => do
      let node ← allNodes[position]?
      let offset ← node.edgeOffset direction
      follow allNodes (position + offset) directions

def neighborhoodAt (allNodes : List (Node WorkLabel degree)) :
    (radius : Nat) → Nat → Option (Neighborhood WorkLabel degree radius)
  | 0, position => (allNodes[position]?).map Node.label
  | radius + 1, position => do
      let node ← allNodes[position]?
      pure (node.label, fun direction => do
        let offset ← node.edgeOffset direction
        neighborhoodAt allNodes radius (position + offset))

def topNeighborhood (scaffold : Scaffold WorkLabel degree) :
    (radius : Nat) → Neighborhood WorkLabel degree radius
  | 0 => scaffold.top.label
  | radius + 1 =>
      (scaffold.top.label, fun direction => do
        let offset ← scaffold.top.edgeOffset direction
        neighborhoodAt scaffold.nodes radius offset)

end Scaffold

inductive LocalTarget (degree radius : Nat) where
  | missing
  | self
  | path (directions : List (Fin degree)) (withinRadius : directions.length ≤ radius)

structure Action (State WorkLabel : Type) (degree radius : Nat) where
  nextState : State
  newLabel : WorkLabel
  target : Fin degree → LocalTarget degree radius

structure Automaton (Terminal : Type) (stateCount workLabelCount degree radius : Nat) where
  degreePositive : 0 < degree
  initialState : Fin stateCount
  accepting : Finset (Fin stateCount)
  transition : Fin stateCount → Terminal → Neighborhood (Fin workLabelCount) degree radius →
    Action (Fin stateCount) (Fin workLabelCount) degree radius

namespace Automaton

variable {Terminal : Type} {stateCount workLabelCount degree radius : Nat}

def initialScaffold : Scaffold (Fin workLabelCount) degree where
  top := { label := none, edgeOffset := fun _ => none }
  older := []

def extendScaffold (old : Scaffold (Fin workLabelCount) degree)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius) :
    Scaffold (Fin workLabelCount) degree where
  top :=
    { label := some action.newLabel
      edgeOffset := fun direction =>
        match action.target direction with
        | .missing => none
        | .self => some 0
        | .path directions _ =>
            (Scaffold.follow old.nodes 0 directions).map (fun endpoint => endpoint + 1) }
  older := old.nodes

def step (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (configuration : Fin stateCount × Scaffold (Fin workLabelCount) degree)
    (symbol : Terminal) :
    Fin stateCount × Scaffold (Fin workLabelCount) degree :=
  let action := automaton.transition configuration.1 symbol
    (configuration.2.topNeighborhood radius)
  (action.nextState, extendScaffold configuration.2 action)

def run (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) :
    Fin stateCount × Scaffold (Fin workLabelCount) degree :=
  input.foldl automaton.step (automaton.initialState, initialScaffold)

def Accepts (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) : Prop :=
  (automaton.run input).1 ∈ automaton.accepting

end Automaton

end Scaffolding

end PegSeparation
