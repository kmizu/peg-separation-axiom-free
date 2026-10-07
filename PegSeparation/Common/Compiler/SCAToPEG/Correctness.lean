import PegSeparation.Common.Compiler.SCAToPEG.Construction
import PegSeparation.Common.Compiler.SCAToPEG.History
import PegSeparation.Common.Compiler.SCAToPEG.Evaluation
import PegSeparation.Common.Compiler.SCAToPEG.Observation
import PegSeparation.Common.Compiler.SCAToPEG.Statements


namespace PegSeparation.SCAToPEG

open PegSeparation
open PegSeparation.Scaffolding

noncomputable section

section Semantics

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
variable {stateCount workLabelCount degree radius : Nat}

def pathResult
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (path : BoundedPath degree radius) (input : List Terminal) :
    ParseResult Terminal :=
  match Scaffold.follow (reverseConfig automaton input).2.nodes 0 path.1 with
  | none => .failure
  | some endpoint => .success (input.drop endpoint)

def nameResult
    (automaton : Automaton Terminal stateCount workLabelCount degree radius) :
    Name stateCount workLabelCount degree radius → List Terminal →
      ParseResult Terminal
  | .state wanted, input =>
      if (reverseConfig automaton input).1 = wanted then .success input else .failure
  | .label wanted, input =>
      if (reverseConfig automaton input).2.top.label = some wanted
        then .success input else .failure
  | .hood wanted, input =>
      if (reverseConfig automaton input).2.topNeighborhood radius = wanted
        then .success input else .failure
  | .path path, input => pathResult automaton path input
  | .consumeAll, _ => .success []
  | .accepts, input =>
      if (reverseConfig automaton input).1 ∈ automaton.accepting
        then .success [] else .failure

def actualKey
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (symbol : Terminal) (rest : List Terminal) :
    TransitionKey Terminal stateCount workLabelCount degree radius where
  state := (reverseConfig automaton rest).1
  symbol := symbol
  view := (reverseConfig automaton rest).2.topNeighborhood radius

@[simp] theorem actionFor_actualKey
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (symbol : Terminal) (rest : List Terminal) :
    actionFor automaton (actualKey automaton symbol rest) =
      automaton.transition (reverseConfig automaton rest).1 symbol
        ((reverseConfig automaton rest).2.topNeighborhood radius) :=
  rfl

@[simp] theorem reverseConfig_cons_state
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (symbol : Terminal) (rest : List Terminal) :
    (reverseConfig automaton (symbol :: rest)).1 =
      (actionFor automaton (actualKey automaton symbol rest)).nextState := by
  simp [reverseConfig_cons, Automaton.step, actionFor, actualKey]

@[simp] theorem reverseConfig_cons_scaffold
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (symbol : Terminal) (rest : List Terminal) :
    (reverseConfig automaton (symbol :: rest)).2 =
      Automaton.extendScaffold (reverseConfig automaton rest).2
        (actionFor automaton (actualKey automaton symbol rest)) := by
  simp [reverseConfig_cons, Automaton.step, actionFor, actualKey]

@[simp] theorem pathResult_emptyPath
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) :
    pathResult automaton (emptyPath degree radius) input = .success input := by
  simp [pathResult, emptyPath, Scaffold.follow, Scaffold.nodes]

theorem follow_extendScaffold_cons
    (old : Scaffold (Fin workLabelCount) degree)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius)
    (direction : Fin degree) (tail : List (Fin degree)) :
    Scaffold.follow (Automaton.extendScaffold old action).nodes 0
        (direction :: tail) =
      match action.target direction with
      | .missing => none
      | .self =>
          Scaffold.follow (Automaton.extendScaffold old action).nodes 0 tail
      | .path directions _ =>
          (Scaffold.follow old.nodes 0 directions).bind fun endpoint =>
            Scaffold.follow (Automaton.extendScaffold old action).nodes
              (endpoint + 1) tail := by
  rw [show (Automaton.extendScaffold old action).nodes =
      (Automaton.extendScaffold old action).top :: old.nodes by rfl]
  simp only [Scaffold.follow, List.getElem?_cons_zero, Nat.zero_add]
  change (match action.target direction with
      | .missing => none
      | .self => some 0
      | .path directions _ =>
          (Scaffold.follow old.nodes 0 directions).map (fun endpoint => endpoint + 1)).bind
      (fun offset => Scaffold.follow
        ((Automaton.extendScaffold old action).top :: old.nodes) offset tail) = _
  cases targetEq : action.target direction with
  | missing =>
      change (none : Option Nat).bind _ = none
      rfl
  | self =>
      change (some 0).bind _ = Scaffold.follow _ 0 tail
      rfl
  | path directions within =>
      change (Option.map (fun endpoint => endpoint + 1)
          (Scaffold.follow old.nodes 0 directions)).bind
            (fun offset => Scaffold.follow
              ((Automaton.extendScaffold old action).top :: old.nodes) offset tail) =
        (Scaffold.follow old.nodes 0 directions).bind fun endpoint =>
          Scaffold.follow ((Automaton.extendScaffold old action).top :: old.nodes)
            (endpoint + 1) tail
      cases Scaffold.follow old.nodes 0 directions <;> rfl

theorem pathResult_cons
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (direction : Fin degree) (tail : BoundedPath degree radius)
    (withinRadius : (direction :: tail.1).length ≤ radius)
    (symbol : Terminal) (rest : List Terminal) :
    pathResult automaton ⟨direction :: tail.1, withinRadius⟩ (symbol :: rest) =
      match (actionFor automaton (actualKey automaton symbol rest)).target direction with
      | .missing => .failure
      | .self => pathResult automaton tail (symbol :: rest)
      | .path directions directionsWithin =>
          match pathResult automaton
              (boundedPathOfList directions directionsWithin) rest with
          | .failure => .failure
          | .success middle => pathResult automaton tail middle := by
  let old := (reverseConfig automaton rest).2
  let action := actionFor automaton (actualKey automaton symbol rest)
  have newScaffold : (reverseConfig automaton (symbol :: rest)).2 =
      Automaton.extendScaffold old action := by
    simpa [old, action] using
      reverseConfig_cons_scaffold automaton symbol rest
  unfold pathResult
  rw [newScaffold]
  rw [follow_extendScaffold_cons]
  cases targetEq : action.target direction with
  | missing =>
      rfl
  | self =>
      rfl
  | path directions directionsWithin =>
      cases oldFollow : Scaffold.follow old.nodes 0 directions with
      | none =>
          simp [oldFollow, old]
      | some endpoint =>
          have endpointLt : endpoint < old.nodes.length :=
            ScaffoldLemmas.follow_result_lt_length oldFollow
          have endpointWithin : endpoint ≤ rest.length := by
            simpa [old, reverseConfig_scaffold_nodes_length automaton rest] using endpointLt
          have shifted := reverseConfig_follow_shift automaton (symbol :: rest)
            (endpoint + 1) (by simp; omega) tail.1
          have dropped : (symbol :: rest).drop (endpoint + 1) = rest.drop endpoint := by
            simp [Nat.add_comm]
          rw [dropped] at shifted
          cases tailFollow : Scaffold.follow
              (reverseConfig automaton (rest.drop endpoint)).2.nodes 0 tail.1 with
          | none =>
              have shiftedNone : Scaffold.follow
                  (Automaton.extendScaffold old action).nodes
                    (endpoint + 1) tail.1 = none := by
                rw [newScaffold] at shifted
                simpa [tailFollow] using shifted
              simp [oldFollow, old, tailFollow, shiftedNone]
          | some tailEndpoint =>
              have shiftedSome : Scaffold.follow
                  (Automaton.extendScaffold old action).nodes
                    (endpoint + 1) tail.1 =
                    some (endpoint + 1 + tailEndpoint) := by
                rw [newScaffold] at shifted
                simpa [tailFollow] using shifted
              have dropEq :
                  (symbol :: rest).drop (endpoint + 1 + tailEndpoint) =
                    (rest.drop endpoint).drop tailEndpoint := by
                rw [List.drop_drop]
                rw [show endpoint + 1 + tailEndpoint =
                  (endpoint + tailEndpoint) + 1 by omega]
                simp only [List.drop_succ_cons]
              simp [oldFollow, old, tailFollow, shiftedSome, dropEq]

def nameRank : Name stateCount workLabelCount degree radius → Nat
  | .state _ => 0
  | .label _ => 0
  | .path path => path.1.length + 1
  | .hood _ => radius + 2
  | .consumeAll => 0
  | .accepts => radius + 3

def nameMeasure
    (name : Name stateCount workLabelCount degree radius)
    (input : List Terminal) : Nat :=
  input.length * (radius + 4) + nameRank name

theorem nameRank_lt
    (name : Name stateCount workLabelCount degree radius) :
    nameRank name < radius + 4 := by
  cases name with
  | state control => simp [nameRank]
  | label work => simp [nameRank]
  | hood view => simp [nameRank]
  | path path =>
      simp only [nameRank]
      omega
  | consumeAll => simp [nameRank]
  | accepts => simp [nameRank]

theorem nameMeasure_lt_of_length_lt
    {first second : List Terminal}
    (lengthLess : first.length < second.length)
    (firstName secondName : Name stateCount workLabelCount degree radius) :
    nameMeasure firstName first < nameMeasure secondName second := by
  unfold nameMeasure
  have firstRank := nameRank_lt firstName
  have nextLength : first.length + 1 ≤ second.length := by omega
  calc
    first.length * (radius + 4) + nameRank firstName <
        first.length * (radius + 4) + (radius + 4) :=
      Nat.add_lt_add_left firstRank _
    _ = (first.length + 1) * (radius + 4) := by
      rw [Nat.add_mul, one_mul]
    _ ≤ second.length * (radius + 4) :=
      Nat.mul_le_mul_right (radius + 4) nextLength
    _ ≤ second.length * (radius + 4) + nameRank secondName :=
      Nat.le_add_right _ _

theorem nameMeasure_lt_of_rank_lt
    (input : List Terminal)
    {firstName secondName : Name stateCount workLabelCount degree radius}
    (rankLess : nameRank firstName < nameRank secondName) :
    nameMeasure firstName input < nameMeasure secondName input := by
  simp [nameMeasure, rankLess]

theorem nameMeasure_lt_of_length_le_rank_lt
    {first second : List Terminal}
    (lengthLess : first.length ≤ second.length)
    {firstName secondName : Name stateCount workLabelCount degree radius}
    (rankLess : nameRank firstName < nameRank secondName) :
    nameMeasure firstName first < nameMeasure secondName second := by
  unfold nameMeasure
  calc
    first.length * (radius + 4) + nameRank firstName ≤
        second.length * (radius + 4) + nameRank firstName :=
      Nat.add_le_add_right (Nat.mul_le_mul_right (radius + 4) lengthLess) _
    _ < second.length * (radius + 4) + nameRank secondName :=
      Nat.add_lt_add_left rankLess _

end Semantics

end

end PegSeparation.SCAToPEG
