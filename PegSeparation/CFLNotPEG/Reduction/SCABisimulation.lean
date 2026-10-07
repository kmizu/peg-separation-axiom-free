import PegSeparation.CFLNotPEG.Reduction.SCACompiler


namespace PegSeparation.Reduction.SCABisimulation

open PegSeparation.Scaffolding
open PegSeparation.Reduction.SCAToCellProbe
open PegSeparation.Reduction.SCACompiler
open PegSeparation.Reduction.SCACompiler.StableGraph

variable {stateCount workLabelCount maxNodes degree radius : ℕ}
variable {Terminal : Type}

def externalRecord
    (scaffold : Scaffold (Fin workLabelCount) degree)
    (locate : ℕ → Option (Fin maxNodes)) (position : ℕ) :
    Option (AbsoluteRecord workLabelCount maxNodes degree) :=
  scaffold.nodes[position]?.map fun node =>
    { label := node.label
      edge := fun port => do
        let offset ← node.edgeOffset port
        locate (position + offset) }

structure Corresponds
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (scaffold : Scaffold (Fin workLabelCount) degree) : Type where
  locate : ℕ → Option (Fin maxNodes)
  root : locate 0 = some graph.root
  allocated : ∀ position node, locate position = some node →
    node.val < graph.count
  record_eq : ∀ position,
    externalRecord scaffold locate position =
      (locate position).map graph.record

namespace Corresponds

theorem present_iff
    {graph : StableGraph stateCount workLabelCount maxNodes degree}
    {scaffold : Scaffold (Fin workLabelCount) degree}
    (relation : Corresponds graph scaffold) (position : ℕ) :
    scaffold.nodes[position]?.isSome = (relation.locate position).isSome := by
  have equality := congrArg Option.isSome (relation.record_eq position)
  simpa [externalRecord] using equality

theorem edge_eq
    {graph : StableGraph stateCount workLabelCount maxNodes degree}
    {scaffold : Scaffold (Fin workLabelCount) degree}
    (relation : Corresponds graph scaffold) (position : ℕ)
    (port : Fin degree) :
    (do
      let node ← scaffold.nodes[position]?
      let offset ← node.edgeOffset port
      relation.locate (position + offset)) =
      (relation.locate position).bind (fun node => graph.edge node port) := by
  cases external : scaffold.nodes[position]? with
  | none =>
      cases located : relation.locate position with
      | none => simp [external, located]
      | some node =>
          have impossible := relation.record_eq position
          simp [externalRecord, external, located] at impossible
  | some externalNode =>
      cases located : relation.locate position with
      | none =>
          have impossible := relation.record_eq position
          simp [externalRecord, external, located] at impossible
      | some node =>
          have recordEquality :
              { label := externalNode.label
                edge := fun port => do
                  let offset ← externalNode.edgeOffset port
                  relation.locate (position + offset) } =
                graph.record node := by
            simpa [externalRecord, external, located] using
              relation.record_eq position
          have edgeEquality := congrFun
            (congrArg AbsoluteRecord.edge recordEquality) port
          simpa [external, located, StableGraph.record] using edgeEquality

theorem label_eq
    {graph : StableGraph stateCount workLabelCount maxNodes degree}
    {scaffold : Scaffold (Fin workLabelCount) degree}
    (relation : Corresponds graph scaffold) (position : ℕ) :
    scaffold.nodes[position]?.map Node.label =
      (relation.locate position).map graph.label := by
  have equality := congrArg
    (Option.map (fun value => value.label))
    (relation.record_eq position)
  simpa [externalRecord, StableGraph.record, Function.comp_def] using equality

end Corresponds


def absoluteFollow
    (graph : StableGraph stateCount workLabelCount maxNodes degree) :
    Fin maxNodes → List (Fin degree) → Option (Fin maxNodes)
  | node, [] => some node
  | node, direction :: directions => do
      let target ← graph.edge node direction
      absoluteFollow graph target directions

theorem Corresponds.follow_eq
    {graph : StableGraph stateCount workLabelCount maxNodes degree}
    {scaffold : Scaffold (Fin workLabelCount) degree}
    (relation : Corresponds graph scaffold)
    (position : ℕ) (directions : List (Fin degree)) :
    (Scaffold.follow scaffold.nodes position directions).bind relation.locate =
      (relation.locate position).bind
        (fun node => absoluteFollow graph node directions) := by
  induction directions generalizing position with
  | nil =>
      have present := relation.present_iff position
      cases external : scaffold.nodes[position]? <;>
        cases located : relation.locate position <;>
        simp [Scaffold.follow, absoluteFollow, external, located] at present ⊢
  | cons direction directions ih =>
      cases external : scaffold.nodes[position]? with
      | none =>
          have edge := relation.edge_eq position direction
          simp [external] at edge
          calc
            (Scaffold.follow scaffold.nodes position
                (direction :: directions)).bind relation.locate = none := by
              simp [Scaffold.follow, external]
            _ = ((relation.locate position).bind
                (fun node => graph.edge node direction)).bind
                  (fun target => absoluteFollow graph target directions) := by
              simpa using congrArg
                (fun target => target.bind
                  (fun node => absoluteFollow graph node directions)) edge
            _ = (relation.locate position).bind fun node =>
                (graph.edge node direction).bind fun target =>
                  absoluteFollow graph target directions := by
              rw [Option.bind_assoc]
      | some node =>
          cases offset : node.edgeOffset direction with
          | none =>
              have edge := relation.edge_eq position direction
              simp [external, offset] at edge
              calc
                (Scaffold.follow scaffold.nodes position
                    (direction :: directions)).bind relation.locate = none := by
                  simp [Scaffold.follow, external, offset]
                _ = ((relation.locate position).bind
                    (fun node => graph.edge node direction)).bind
                      (fun target => absoluteFollow graph target directions) := by
                  simpa using congrArg
                    (fun target => target.bind
                      (fun node => absoluteFollow graph node directions)) edge
                _ = (relation.locate position).bind fun node =>
                    (graph.edge node direction).bind fun target =>
                      absoluteFollow graph target directions := by
                  rw [Option.bind_assoc]
          | some offsetValue =>
              have edge := relation.edge_eq position direction
              simp [external, offset] at edge
              simp [Scaffold.follow, absoluteFollow, external, offset,
                ih (position + offsetValue), edge, Option.bind_assoc]

theorem resolve_locatedView_eq_follow
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (node : Fin maxNodes) (directions : List (Fin degree))
    (within : directions.length ≤ radius) :
    (graph.locatedView radius node).resolve directions within =
      absoluteFollow graph node directions := by
  induction radius generalizing node directions with
  | zero =>
      cases directions with
      | nil => rfl
      | cons direction directions => simp at within
  | succ radius ih =>
      cases directions with
      | nil => rfl
      | cons direction directions =>
          simp only [StableGraph.locatedView,
            LocatedNeighborhood.resolve, absoluteFollow]
          cases edge : graph.edge node direction with
          | none => rfl
          | some target =>
              simp only [edge]
              exact ih target directions
                (Nat.le_of_succ_le_succ within)

theorem Corresponds.neighborhoodAt_eq
    {graph : StableGraph stateCount workLabelCount maxNodes degree}
    {scaffold : Scaffold (Fin workLabelCount) degree}
    (relation : Corresponds graph scaffold)
    (viewRadius : ℕ) (position : ℕ) :
    Scaffold.neighborhoodAt scaffold.nodes viewRadius position =
      (relation.locate position).map fun node =>
        (graph.locatedView viewRadius node).erase := by
  induction viewRadius generalizing position with
  | zero =>
      change scaffold.nodes[position]?.map Node.label =
        (relation.locate position).map graph.label
      exact relation.label_eq position
  | succ viewRadius ih =>
      cases external : scaffold.nodes[position]? with
      | none =>
          have present := relation.present_iff position
          cases located : relation.locate position with
          | none => simp [Scaffold.neighborhoodAt, external, located]
          | some node => simp [external, located] at present
      | some externalNode =>
          have present := relation.present_iff position
          cases located : relation.locate position with
          | none => simp [external, located] at present
          | some node =>
              have labels := relation.label_eq position
              simp [external, located] at labels
              simp [Scaffold.neighborhoodAt, external, located,
                StableGraph.locatedView, LocatedNeighborhood.erase]
              apply Prod.ext
              · exact labels
              · funext port
                cases offset : externalNode.edgeOffset port with
                | none =>
                    have edge := relation.edge_eq position port
                    simp [external, located, offset] at edge
                    simp only [offset, Option.bind_none]
                    rw [← edge]
                | some offsetValue =>
                    have edge := relation.edge_eq position port
                    simp [external, located, offset] at edge
                    simp [offset, ih (position + offsetValue), edge]
                    cases graph.edge node port <;> rfl

@[simp] theorem neighborhoodAt_zero
    (scaffold : Scaffold (Fin workLabelCount) degree)
    (viewRadius : ℕ) :
    Scaffold.neighborhoodAt scaffold.nodes viewRadius 0 =
      some (scaffold.topNeighborhood viewRadius) := by
  cases viewRadius with
  | zero => rfl
  | succ viewRadius =>
      simp [Scaffold.neighborhoodAt, Scaffold.topNeighborhood,
        Scaffold.nodes]

theorem Corresponds.topNeighborhood_eq
    {graph : StableGraph stateCount workLabelCount maxNodes degree}
    {scaffold : Scaffold (Fin workLabelCount) degree}
    (relation : Corresponds graph scaffold) (viewRadius : ℕ) :
    scaffold.topNeighborhood viewRadius =
      (graph.locatedView viewRadius graph.root).erase := by
  have neighborhoods := relation.neighborhoodAt_eq viewRadius 0
  rw [neighborhoodAt_zero, relation.root] at neighborhoods
  exact Option.some.inj neighborhoods


def prependLocate (fresh : Fin maxNodes)
    (locate : ℕ → Option (Fin maxNodes)) : ℕ → Option (Fin maxNodes)
  | 0 => some fresh
  | position + 1 => locate position

@[simp] theorem prependLocate_zero (fresh : Fin maxNodes) (locate) :
    prependLocate fresh locate 0 = some fresh := rfl

@[simp] theorem prependLocate_succ (fresh : Fin maxNodes) (locate) (position : ℕ) :
    prependLocate fresh locate (position + 1) = locate position := rfl

theorem bind_shift_prependLocate (fresh : Fin maxNodes)
    (locate : ℕ → Option (Fin maxNodes)) (endpoint : Option ℕ) :
    (endpoint.map (fun position => position + 1)).bind
        (prependLocate fresh locate) =
      endpoint.bind locate := by
  cases endpoint <;> rfl

theorem Corresponds.follow_from_root
    {graph : StableGraph stateCount workLabelCount maxNodes degree}
    {scaffold : Scaffold (Fin workLabelCount) degree}
    (relation : Corresponds graph scaffold)
    (directions : List (Fin degree)) :
    (Scaffold.follow scaffold.nodes 0 directions).bind relation.locate =
      absoluteFollow graph graph.root directions := by
  rw [relation.follow_eq, relation.root]
  rfl

theorem Corresponds.follow_from_root_eq_resolve
    {graph : StableGraph stateCount workLabelCount maxNodes degree}
    {scaffold : Scaffold (Fin workLabelCount) degree}
    (relation : Corresponds graph scaffold)
    (directions : List (Fin degree))
    (within : directions.length ≤ radius) :
    (Scaffold.follow scaffold.nodes 0 directions).bind relation.locate =
      (graph.locatedView radius graph.root).resolve directions within := by
  rw [relation.follow_from_root]
  exact (resolve_locatedView_eq_follow graph graph.root directions within).symm

theorem externalRecord_extend_succ
    (scaffold : Scaffold (Fin workLabelCount) degree)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius)
    (fresh : Fin maxNodes) (locate : ℕ → Option (Fin maxNodes))
    (position : ℕ) :
    externalRecord (Scaffolding.Automaton.extendScaffold scaffold action)
        (prependLocate fresh locate) (position + 1) =
      externalRecord scaffold locate position := by
  have nodes :
      (Scaffolding.Automaton.extendScaffold scaffold action).nodes[position + 1]? =
        scaffold.nodes[position]? := by
    simp [Scaffolding.Automaton.extendScaffold, Scaffold.nodes]
  unfold externalRecord
  rw [nodes]
  cases present : scaffold.nodes[position]? with
  | none => rfl
  | some node =>
      simp only [Option.map_some]
      apply congrArg some
      apply AbsoluteRecord.ext
      · rfl
      · funext port
        cases offset : node.edgeOffset port with
        | none => simp [offset]
        | some offsetValue =>
            simp [offset, Nat.succ_add, prependLocate_succ]

theorem Corresponds.externalRecord_extend_zero
    {graph : StableGraph stateCount workLabelCount maxNodes degree}
    {scaffold : Scaffold (Fin workLabelCount) degree}
    (relation : Corresponds graph scaffold)
    (room : graph.count < maxNodes)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius) :
    externalRecord (Scaffolding.Automaton.extendScaffold scaffold action)
        (prependLocate ⟨graph.count, room⟩ relation.locate) 0 =
      some
        { label := some action.newLabel
          edge := fun port => resolveTarget ⟨graph.count, room⟩
            (graph.locatedView radius graph.root) (action.target port) } := by
  apply congrArg some
  apply AbsoluteRecord.ext
  · rfl
  · funext port
    cases target : action.target port with
    | missing =>
        simp [externalRecord, Scaffolding.Automaton.extendScaffold,
          Scaffold.nodes, prependLocate, resolveTarget, target]
    | self =>
        simp [externalRecord, Scaffolding.Automaton.extendScaffold,
          Scaffold.nodes, prependLocate, resolveTarget, target]
    | path directions within =>
        simp [externalRecord, Scaffolding.Automaton.extendScaffold,
          Scaffold.nodes, resolveTarget, target,
          bind_shift_prependLocate]
        exact relation.follow_from_root_eq_resolve directions within

theorem appendAction_record_fresh
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (room : graph.count < maxNodes)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius) :
    (graph.appendAction room view action).record ⟨graph.count, room⟩ =
      { label := some action.newLabel
        edge := fun port => resolveTarget ⟨graph.count, room⟩ view
          (action.target port) } := by
  apply AbsoluteRecord.ext
  · simp [StableGraph.record, StableGraph.appendAction]
  · funext port
    simp [StableGraph.record, StableGraph.appendAction]

theorem appendAction_record_old
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (room : graph.count < maxNodes)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius)
    (node : Fin maxNodes) (old : node ≠ ⟨graph.count, room⟩) :
    (graph.appendAction room view action).record node = graph.record node := by
  apply AbsoluteRecord.ext
  · simp [StableGraph.record, StableGraph.appendAction, old]
  · funext port
    simp [StableGraph.record, StableGraph.appendAction, old]

noncomputable def Corresponds.append
    {graph : StableGraph stateCount workLabelCount maxNodes degree}
    {scaffold : Scaffold (Fin workLabelCount) degree}
    (relation : Corresponds graph scaffold)
    (room : graph.count < maxNodes)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius) :
    Corresponds
      (graph.appendAction room (graph.locatedView radius graph.root) action)
      (Scaffolding.Automaton.extendScaffold scaffold action) := by
  let fresh : Fin maxNodes := ⟨graph.count, room⟩
  refine
    { locate := prependLocate fresh relation.locate
      root := ?_
      allocated := ?_
      record_eq := ?_ }
  · exact congrArg some
      (StableGraph.appendAction_root graph room
        (graph.locatedView radius graph.root) action).symm
  · intro position node located
    cases position with
    | zero =>
        simp [prependLocate, fresh] at located
        subst node
        simp [StableGraph.appendAction, fresh]
    | succ position =>
        have oldLocated : relation.locate position = some node := by
          simpa [prependLocate, fresh] using located
        have allocated := relation.allocated position node oldLocated
        simpa [StableGraph.appendAction] using Nat.lt_succ_of_lt allocated
  · intro position
    cases position with
    | zero =>
        rw [relation.externalRecord_extend_zero room action]
        simp only [prependLocate_zero, Option.map_some]
        exact congrArg some
          (appendAction_record_fresh graph room
            (graph.locatedView radius graph.root) action).symm
    | succ position =>
        rw [externalRecord_extend_succ]
        simp only [prependLocate_succ]
        cases located : relation.locate position with
        | none => simpa [located] using relation.record_eq position
        | some node =>
            have allocated := relation.allocated position node located
            have old : node ≠ ⟨graph.count, room⟩ := by
              intro equality
              have values := congrArg Fin.val equality
              simp at values
              omega
            simp only [Option.map_some]
            rw [appendAction_record_old graph room
              (graph.locatedView radius graph.root) action node old]
            have oldRecord := relation.record_eq position
            rw [located] at oldRecord
            exact oldRecord


structure ConfigurationCorresponds
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (configuration : Fin stateCount × Scaffold (Fin workLabelCount) degree) :
    Type where
  control_eq : graph.control = configuration.1
  scaffold : Corresponds graph configuration.2

noncomputable def stableStep
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (room : graph.count < maxNodes) (symbol : Terminal) :
    StableGraph stateCount workLabelCount maxNodes degree :=
  let view := graph.locatedView radius graph.root
  let action := automaton.transition graph.control symbol view.erase
  graph.appendAction room view action

@[simp] theorem stableStep_count
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (room : graph.count < maxNodes) (symbol : Terminal) :
    (stableStep automaton graph room symbol).count = graph.count + 1 := rfl

noncomputable def ConfigurationCorresponds.step
    {graph : StableGraph stateCount workLabelCount maxNodes degree}
    {configuration : Fin stateCount ×
      Scaffold (Fin workLabelCount) degree}
    (relation : ConfigurationCorresponds graph configuration)
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (room : graph.count < maxNodes) (symbol : Terminal) :
    ConfigurationCorresponds
      (stableStep automaton graph room symbol)
      (automaton.step configuration symbol) := by
  have neighborhood := relation.scaffold.topNeighborhood_eq radius
  have actionEquality :
      automaton.transition configuration.1 symbol
          (configuration.2.topNeighborhood radius) =
        automaton.transition graph.control symbol
          (graph.locatedView radius graph.root).erase := by
    rw [← relation.control_eq, neighborhood]
  refine
    { control_eq := ?_
      scaffold := ?_ }
  · simp [stableStep, Scaffolding.Automaton.step, actionEquality,
      StableGraph.appendAction]
  · simpa [stableStep, Scaffolding.Automaton.step, actionEquality] using
      relation.scaffold.append room
        (automaton.transition graph.control symbol
          (graph.locatedView radius graph.root).erase)


def initialGraph (initialState : Fin stateCount) (capacity : 0 < maxNodes) :
    StableGraph stateCount workLabelCount maxNodes degree :=
  { control := initialState
    count := 1
    count_pos := Nat.zero_lt_one
    count_le := capacity
    label := fun _ => none
    edge := fun _ _ => none }

def initialLocate (capacity : 0 < maxNodes) : ℕ → Option (Fin maxNodes)
  | 0 => some ⟨0, capacity⟩
  | _ + 1 => none

def initialCorrespondence
    (initialState : Fin stateCount) (capacity : 0 < maxNodes) :
    Corresponds
      (initialGraph (workLabelCount := workLabelCount) (degree := degree)
        initialState capacity)
      (Scaffolding.Automaton.initialScaffold
        (workLabelCount := workLabelCount) (degree := degree)) := by
  refine
    { locate := initialLocate capacity
      root := ?_
      allocated := ?_
      record_eq := ?_ }
  · apply congrArg some
    apply Fin.ext
    rfl
  · intro position node located
    cases position with
    | zero =>
        simp [initialLocate] at located
        subst node
        exact Nat.zero_lt_one
    | succ position => simp [initialLocate] at located
  · intro position
    cases position with
    | zero =>
        simp [externalRecord, initialLocate, initialGraph,
          Scaffolding.Automaton.initialScaffold, Scaffold.nodes,
          StableGraph.record]
    | succ position =>
        simp [externalRecord, initialLocate, initialGraph,
          Scaffolding.Automaton.initialScaffold, Scaffold.nodes]

def initialConfigurationCorrespondence
    (initialState : Fin stateCount) (capacity : 0 < maxNodes) :
    ConfigurationCorresponds
      (initialGraph (workLabelCount := workLabelCount) (degree := degree)
        initialState capacity)
      (initialState,
        Scaffolding.Automaton.initialScaffold
          (workLabelCount := workLabelCount) (degree := degree)) :=
  { control_eq := rfl
    scaffold := initialCorrespondence initialState capacity }


noncomputable def runCorrespondence
    (automaton : Automaton Terminal stateCount workLabelCount degree radius) :
    {graph : StableGraph stateCount workLabelCount maxNodes degree} →
    {configuration : Fin stateCount ×
      Scaffold (Fin workLabelCount) degree} →
    ConfigurationCorresponds graph configuration →
    (input : List Terminal) →
    graph.count + input.length ≤ maxNodes →
    Σ finalGraph : StableGraph stateCount workLabelCount maxNodes degree,
      ConfigurationCorresponds finalGraph
        (QueryOverlay.runFrom automaton configuration input)
  | graph, configuration, relation, [], _ => ⟨graph, relation⟩
  | graph, configuration, relation, symbol :: rest, space =>
      let room : graph.count < maxNodes := by
        simp only [List.length_cons] at space
        omega
      let nextRelation := relation.step automaton room symbol
      have nextSpace :
          (stableStep automaton graph room symbol).count + rest.length ≤
            maxNodes := by
        rw [stableStep_count]
        simp only [List.length_cons] at space
        omega
      runCorrespondence automaton nextRelation rest nextSpace

theorem runCorrespondence_count
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    {graph : StableGraph stateCount workLabelCount maxNodes degree}
    {configuration : Fin stateCount × Scaffold (Fin workLabelCount) degree}
    (relation : ConfigurationCorresponds graph configuration)
    (input : List Terminal)
    (space : graph.count + input.length ≤ maxNodes) :
    (runCorrespondence automaton relation input space).1.count =
      graph.count + input.length := by
  induction input generalizing graph configuration with
  | nil => rfl
  | cons symbol rest ih =>
      let room : graph.count < maxNodes := by
        simp only [List.length_cons] at space
        omega
      let nextRelation := relation.step automaton room symbol
      have nextSpace :
          (stableStep automaton graph room symbol).count + rest.length ≤
            maxNodes := by
        rw [stableStep_count]
        simp only [List.length_cons] at space
        omega
      change
        (runCorrespondence automaton nextRelation rest nextSpace).1.count =
          graph.count + (symbol :: rest).length
      rw [ih nextRelation nextSpace, stableStep_count]
      simp only [List.length_cons]
      omega

noncomputable def initialRunCorrespondence
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) (space : input.length + 1 ≤ maxNodes) :
    Σ finalGraph : StableGraph stateCount workLabelCount maxNodes degree,
      ConfigurationCorresponds finalGraph (automaton.run input) := by
  have capacity : 0 < maxNodes := by omega
  have initialSpace :
      (initialGraph (workLabelCount := workLabelCount) (degree := degree)
        automaton.initialState capacity).count + input.length ≤ maxNodes := by
    simp [initialGraph]
    omega
  let result := runCorrespondence automaton
    (initialConfigurationCorrespondence automaton.initialState capacity)
    input initialSpace
  refine ⟨result.1, ?_⟩
  rw [← QueryOverlay.runFrom_initial automaton input]
  exact result.2

theorem initialRun_control_eq
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) (space : input.length + 1 ≤ maxNodes) :
    (initialRunCorrespondence automaton input space).1.control =
      (automaton.run input).1 :=
  (initialRunCorrespondence automaton input space).2.control_eq

theorem initialRunCorrespondence_count
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) (space : input.length + 1 ≤ maxNodes) :
    (initialRunCorrespondence automaton input space).1.count =
      input.length + 1 := by
  unfold initialRunCorrespondence
  dsimp only
  rw [runCorrespondence_count]
  simp [initialGraph]
  omega

end PegSeparation.Reduction.SCABisimulation
