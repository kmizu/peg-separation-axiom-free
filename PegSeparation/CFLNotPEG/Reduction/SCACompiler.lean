import PegSeparation.CFLNotPEG.Reduction.SCAToCellProbe


namespace PegSeparation.Reduction.SCACompiler

open PegSeparation.Scaffolding
open PegSeparation.CellProbe
open PegSeparation.Reduction.SCAToCellProbe


structure StableGraph
    (stateCount workLabelCount maxNodes degree : ℕ) where
  control : Fin stateCount
  count : ℕ
  count_pos : 0 < count
  count_le : count ≤ maxNodes
  label : Fin maxNodes → Option (Fin workLabelCount)
  edge : Fin maxNodes → Fin degree → Option (Fin maxNodes)

namespace StableGraph

variable {stateCount workLabelCount maxNodes degree : ℕ}

def root (graph : StableGraph stateCount workLabelCount maxNodes degree) :
    Fin maxNodes :=
  ⟨graph.count - 1,
    (Nat.pred_lt (Nat.ne_of_gt graph.count_pos)).trans_le graph.count_le⟩

structure AbsoluteRecord (workLabelCount maxNodes degree : ℕ) where
  label : Option (Fin workLabelCount)
  edge : Fin degree → Option (Fin maxNodes)

@[ext] theorem AbsoluteRecord.ext
    {left right : AbsoluteRecord workLabelCount maxNodes degree}
    (label : left.label = right.label)
    (edge : left.edge = right.edge) : left = right := by
  cases left
  cases right
  cases label
  cases edge
  rfl

def record (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (node : Fin maxNodes) : AbsoluteRecord workLabelCount maxNodes degree :=
  { label := graph.label node
    edge := graph.edge node }


mutual
  inductive LocatedNeighborhood
      (workLabelCount maxNodes degree : ℕ) : ℕ → Type
    | leaf (node : Fin maxNodes) (label : Option (Fin workLabelCount)) :
        LocatedNeighborhood workLabelCount maxNodes degree 0
    | branch {radius : ℕ} (node : Fin maxNodes)
        (label : Option (Fin workLabelCount))
        (child : Fin degree →
          LocatedChild workLabelCount maxNodes degree radius) :
        LocatedNeighborhood workLabelCount maxNodes degree (radius + 1)

  inductive LocatedChild
      (workLabelCount maxNodes degree : ℕ) : ℕ → Type
    | missing {radius : ℕ} :
        LocatedChild workLabelCount maxNodes degree radius
    | present {radius : ℕ}
        (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
        : LocatedChild workLabelCount maxNodes degree radius
end

namespace LocatedNeighborhood

def node {radius : ℕ}
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius) :
    Fin maxNodes :=
  match view with
  | .leaf node _ => node
  | .branch node _ _ => node

def erase : {radius : ℕ} →
    LocatedNeighborhood workLabelCount maxNodes degree radius →
      Neighborhood (Fin workLabelCount) degree radius
  | 0, .leaf _ label => label
  | _ + 1, .branch _ label child =>
      (label, fun port =>
        match child port with
        | .missing => none
        | .present view => some view.erase)

def resolve : {radius : ℕ} →
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius) →
    (directions : List (Fin degree)) → directions.length ≤ radius →
      Option (Fin maxNodes)
  | _, view, [], _ => some view.node
  | 0, .leaf _ _, _ :: _, within => by simp at within
  | radius + 1, .branch _ _ child, direction :: rest, within =>
      match child direction with
      | .missing => none
      | .present next =>
          resolve next rest (by simpa using Nat.le_of_succ_le_succ within)

end LocatedNeighborhood

def locatedView (graph : StableGraph stateCount workLabelCount maxNodes degree) :
    (radius : ℕ) → Fin maxNodes →
      LocatedNeighborhood workLabelCount maxNodes degree radius
  | 0, node => .leaf node (graph.label node)
  | radius + 1, node =>
      .branch node (graph.label node) (fun port =>
        match graph.edge node port with
        | none => .missing
        | some target => .present (locatedView graph radius target))

def emptyLocated : (radius : ℕ) → Fin maxNodes →
    LocatedNeighborhood workLabelCount maxNodes degree radius
  | 0, node => .leaf node none
  | radius + 1, node => .branch node none (fun _ => .missing)

def LocatedChild.getD {radius : ℕ}
    (child : LocatedChild workLabelCount maxNodes degree radius)
    (fallbackNode : Fin maxNodes) :
    LocatedNeighborhood workLabelCount maxNodes degree radius :=
  match child with
  | .missing => emptyLocated radius fallbackNode
  | .present view => view

def resolveTarget {radius : ℕ} (fresh : Fin maxNodes)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius) :
    LocalTarget degree radius → Option (Fin maxNodes)
  | .missing => none
  | .self => some fresh
  | .path directions within => view.resolve directions within

noncomputable def appendAction {radius : ℕ}
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (room : graph.count < maxNodes)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius) :
    StableGraph stateCount workLabelCount maxNodes degree :=
  let fresh : Fin maxNodes := ⟨graph.count, room⟩
  { control := action.nextState
    count := graph.count + 1
    count_pos := Nat.succ_pos _
    count_le := room
    label := Function.update graph.label fresh (some action.newLabel)
    edge := Function.update graph.edge fresh
      (fun port => resolveTarget fresh view (action.target port)) }

@[simp] theorem appendAction_count {radius : ℕ}
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (room : graph.count < maxNodes)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius) :
    (appendAction graph room view action).count = graph.count + 1 := rfl

theorem appendAction_root {radius : ℕ}
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (room : graph.count < maxNodes)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius) :
    (appendAction graph room view action).root = ⟨graph.count, room⟩ := by
  apply Fin.ext
  simp [root, appendAction]

end StableGraph


namespace GraphPacking

open StableGraph
open PegSeparation.Reduction.SCAToCellProbe.Packing

variable {wordBits maxNodes stateCount workLabelCount degree : ℕ}

noncomputable def graphWord
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (graph : StableGraph stateCount workLabelCount maxNodes degree) :
    LogicalAddress maxNodes degree → CellProbe.Word wordBits
  | .state => packing.stateWord graph.control
  | .nodeLabel node => packing.labelWord (graph.label node)
  | .nodeEdge node port => packing.offsetWord (graph.edge node port)

def Represents
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (memory : FiniteMemory wordBits)
    (graph : StableGraph stateCount workLabelCount maxNodes degree) : Prop :=
  ∀ logical,
    memory (packing.address logical) = GraphPacking.graphWord packing graph logical

noncomputable def encodeGraph
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (graph : StableGraph stateCount workLabelCount maxNodes degree) :
    FiniteMemory wordBits := fun physical =>
  if existsLogical : ∃ logical, packing.address logical = physical then
    GraphPacking.graphWord packing graph (Classical.choose existsLogical)
  else
    0

theorem encodeGraph_read
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (logical : LogicalAddress maxNodes degree) :
    GraphPacking.encodeGraph packing graph (packing.address logical) =
      GraphPacking.graphWord packing graph logical := by
  classical
  unfold encodeGraph
  split
  next existsLogical =>
    have chosen_eq : Classical.choose existsLogical = logical :=
      packing.address_injective (Classical.choose_spec existsLogical)
    rw [chosen_eq]
  next noLogical => exact (noLogical ⟨logical, rfl⟩).elim

theorem encodeGraph_represents
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (graph : StableGraph stateCount workLabelCount maxNodes degree) :
    GraphPacking.Represents packing (GraphPacking.encodeGraph packing graph) graph :=
  GraphPacking.encodeGraph_read packing graph

noncomputable def decodeLabel
    (word : CellProbe.Word wordBits) : Option (Fin workLabelCount) :=
  (unpackFinite word : Option (Option (Fin workLabelCount))).getD none

noncomputable def decodeEdge
    (word : CellProbe.Word wordBits) : Option (Fin maxNodes) :=
  (unpackFinite word : Option (Option (Fin maxNodes))).getD none

@[simp] theorem decodeLabel_labelWord
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (label : Option (Fin workLabelCount)) :
    decodeLabel (packing.labelWord label) = label := by
  simp [decodeLabel, Packing.labelWord]

@[simp] theorem decodeEdge_offsetWord
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (edge : Option (Fin maxNodes)) :
    decodeEdge (packing.offsetWord edge) = edge := by
  simp [decodeEdge, Packing.offsetWord]

noncomputable def decodeRecord
    (words : List (CellProbe.Word wordBits)) :
    AbsoluteRecord workLabelCount maxNodes degree :=
  { label := decodeLabel (words[0]?.getD 0)
    edge := fun port => decodeEdge (words[port.val + 1]?.getD 0) }

noncomputable def readRecord
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (node : Fin maxNodes) :
    ReadProgram wordBits (AbsoluteRecord workLabelCount maxNodes degree)
      (packing.nodeRecordAddresses node).length :=
  (ReadProgram.readCells (packing.nodeRecordAddresses node)).map decodeRecord

noncomputable def recordWords
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (node : Fin maxNodes) : List (CellProbe.Word wordBits) :=
  (nodeRecordLogical (degree := degree) node).map
    (GraphPacking.graphWord packing graph)

theorem decodeRecord_recordWords
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (node : Fin maxNodes) :
    decodeRecord (GraphPacking.recordWords packing graph node) =
      graph.record node := by
  apply AbsoluteRecord.ext
  · simp [decodeRecord, recordWords, nodeRecordLogical, graphWord,
      StableGraph.record]
  · funext port
    simp [decodeRecord, recordWords, nodeRecordLogical, graphWord,
      StableGraph.record]

theorem readRecord_correct
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (memory : FiniteMemory wordBits)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (represents : GraphPacking.Represents packing memory graph)
    (node : Fin maxNodes) :
    ((GraphPacking.readRecord packing node).execute memory).result =
      graph.record node := by
  rw [readRecord, ReadProgram.map_execute_result,
    ReadProgram.readCells_result]
  change decodeRecord
      (List.map memory (List.map packing.address
        (nodeRecordLogical (degree := degree) node))) = _
  rw [List.map_map]
  have pointwise :
      List.map (fun logical => memory (packing.address logical))
          (nodeRecordLogical (degree := degree) node) =
        GraphPacking.recordWords packing graph node := by
    apply List.map_congr_left
    intro logical membership
    exact represents logical
  have pointwise' :
      List.map (memory ∘ packing.address)
          (nodeRecordLogical (degree := degree) node) =
        GraphPacking.recordWords packing graph node := by
    simpa [Function.comp_def] using pointwise
  rw [pointwise', decodeRecord_recordWords]

noncomputable def readRecordFixed
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (node : Fin maxNodes) :
    ReadProgram wordBits (AbsoluteRecord workLabelCount maxNodes degree)
      (degree + 1) :=
  cast (congrArg
      (ReadProgram wordBits (AbsoluteRecord workLabelCount maxNodes degree))
      (packing.nodeRecordAddresses_length node))
    (GraphPacking.readRecord packing node)

theorem readRecordFixed_correct
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (memory : FiniteMemory wordBits)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (represents : GraphPacking.Represents packing memory graph)
    (node : Fin maxNodes) :
    ((GraphPacking.readRecordFixed packing node).execute memory).result =
      graph.record node := by
  rw [readRecordFixed,
    ReadProgram.execute_cast (packing.nodeRecordAddresses_length node)
      (GraphPacking.readRecord packing node) memory]
  exact GraphPacking.readRecord_correct packing memory graph represents node

end GraphPacking


namespace ViewCompiler

open StableGraph

variable {wordBits maxNodes stateCount workLabelCount degree : ℕ}

def finBudget (each : ℕ) : ℕ → ℕ
  | 0 => 0
  | degree + 1 => finBudget each degree + each

theorem finBudget_eq_mul (each degree : ℕ) :
    finBudget each degree = degree * each := by
  induction degree with
  | zero => simp [finBudget]
  | succ degree ih => simp [finBudget, ih, Nat.succ_mul]

def traverseFin {Output : Type} {each : ℕ} :
    (degree : ℕ) →
    (Fin degree → ReadProgram wordBits Output each) →
      ReadProgram wordBits (Fin degree → Output) (finBudget each degree)
  | 0, _ => .done Fin.elim0
  | degree + 1, program =>
      (program 0).bind fun head =>
        (traverseFin degree (fun port => program port.succ)).map
          (Fin.cons head)

theorem traverseFin_execute_result {Output : Type} {each : ℕ}
    (memory : FiniteMemory wordBits) (degree : ℕ)
    (program : Fin degree → ReadProgram wordBits Output each) :
    ((traverseFin degree program).execute memory).result =
      fun port => (program port).execute memory |>.result := by
  induction degree with
  | zero =>
      funext port
      exact Fin.elim0 port
  | succ degree ih =>
      change
        (((program 0).bind fun head =>
          (traverseFin degree (fun port => program port.succ)).map
            (fun tail : Fin degree → Output =>
              (Fin.cons head tail : Fin (degree + 1) → Output))).execute
                memory).result = _
      rw [ReadProgram.bind_execute_result,
        ReadProgram.map_execute_result]
      funext port
      refine Fin.cases ?_ (fun tail => ?_) port
      · rfl
      · exact congrFun (ih (fun p => program p.succ)) tail

def viewBudget (degree : ℕ) : ℕ → ℕ
  | 0 => degree + 1
  | radius + 1 => finBudget (viewBudget degree radius) degree + (degree + 1)

theorem viewBudget_eq (degree radius : ℕ) :
    viewBudget degree radius =
      (degree + 1) * pathOccurrences degree radius := by
  induction radius with
  | zero => simp [viewBudget, pathOccurrences]
  | succ radius ih =>
      rw [viewBudget, finBudget_eq_mul, ih, pathOccurrences]
      ring

noncomputable def compileView
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits) :
    (radius : ℕ) → Option (Fin maxNodes) →
      ReadProgram wordBits
        (LocatedChild workLabelCount maxNodes degree radius)
        (viewBudget degree radius)
  | radius, none =>
      ReadProgram.pad dummyAddress .missing (viewBudget degree radius)
  | 0, some node =>
      (GraphPacking.readRecordFixed packing node).map fun record =>
        .present (.leaf node record.label)
  | radius + 1, some node =>
      (GraphPacking.readRecordFixed packing node).bind fun record =>
        (traverseFin degree (fun port =>
          compileView packing dummyAddress radius (record.edge port))).map
          fun children => .present (.branch node record.label children)

def semanticView
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (radius : ℕ) : Option (Fin maxNodes) →
      LocatedChild workLabelCount maxNodes degree radius
  | none => .missing
  | some node => .present (graph.locatedView radius node)

theorem compileView_correct
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (memory : FiniteMemory wordBits)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (represents : GraphPacking.Represents packing memory graph)
    (radius : ℕ) (cursor : Option (Fin maxNodes)) :
    ((compileView packing dummyAddress radius cursor).execute memory).result =
      semanticView graph radius cursor := by
  induction radius generalizing cursor with
  | zero =>
      cases cursor with
      | none => simp [compileView, semanticView, ReadProgram.pad_execute_result]
      | some node =>
          change
            (((GraphPacking.readRecordFixed packing node).map fun record =>
              LocatedChild.present (.leaf node record.label)).execute
                memory).result = _
          rw [ReadProgram.map_execute_result,
            GraphPacking.readRecordFixed_correct packing memory graph
              represents node]
          rfl
  | succ radius ih =>
      cases cursor with
      | none => simp [compileView, semanticView, ReadProgram.pad_execute_result]
      | some node =>
          change
            (((GraphPacking.readRecordFixed packing node).bind fun record =>
              (traverseFin degree (fun port =>
                compileView packing dummyAddress radius
                  (record.edge port))).map fun children =>
                    LocatedChild.present
                      (.branch node record.label children)).execute
                        memory).result = _
          rw [ReadProgram.bind_execute_result,
            GraphPacking.readRecordFixed_correct packing memory graph
              represents node,
            ReadProgram.map_execute_result, traverseFin_execute_result]
          simp only [semanticView, StableGraph.locatedView]
          congr 3
          funext port
          exact ih (graph.edge node port)

end ViewCompiler


namespace StepCompiler

open StableGraph
open ViewCompiler

variable {Terminal : Type}
  {wordBits maxNodes stateCount workLabelCount degree radius : ℕ}

noncomputable def decodeState
    (fallback : Fin stateCount) (word : CellProbe.Word wordBits) :
    Fin stateCount :=
  (unpackFinite word : Option (Fin stateCount)).getD fallback

@[simp] theorem decodeState_stateWord
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (fallback state : Fin stateCount) :
    decodeState fallback (packing.stateWord state) = state := by
  simp [decodeState, Packing.stateWord]

noncomputable def readStateAndView
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (root : Fin maxNodes) :
    ReadProgram wordBits
      (Fin stateCount × LocatedNeighborhood workLabelCount maxNodes degree radius)
      (viewBudget degree radius + 1) :=
  (ReadProgram.readCell (packing.address .state)).bind fun stateWord =>
    (compileView packing dummyAddress radius (some root)).map fun loaded =>
      (decodeState automaton.initialState stateWord, loaded.getD root)

theorem readStateAndView_correct
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (memory : FiniteMemory wordBits)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (represents : GraphPacking.Represents packing memory graph) :
    ((readStateAndView automaton packing dummyAddress graph.root).execute memory).result =
      (graph.control, graph.locatedView radius graph.root) := by
  rw [readStateAndView, ReadProgram.bind_execute_result,
    ReadProgram.map_execute_result]
  have stateRead : memory (packing.address (.state : LogicalAddress maxNodes degree)) =
      packing.stateWord graph.control := represents .state
  rw [ReadProgram.readCell_result, stateRead, decodeState_stateWord]
  rw [compileView_correct packing dummyAddress memory graph represents]
  rfl

def writeFin {Result : Type} (result : Result) :
    (degree : ℕ) → (Fin degree → WriteEntry wordBits) →
      UpdateProgram wordBits Result 0 (finBudget 1 degree)
  | 0, _ => .done result
  | degree + 1, entries =>
      let head := entries 0
      .write head.address head.value
        (writeFin result degree (fun port => entries port.succ))

@[simp] theorem writeFin_execute_result {Result : Type} (result : Result)
    (degree : ℕ) (entries : Fin degree → WriteEntry wordBits)
    (memory : FiniteMemory wordBits) :
    ((writeFin result degree entries).execute memory).result = result := by
  induction degree generalizing memory with
  | zero => rfl
  | succ degree ih =>
      change
        ((writeFin result degree (fun port => entries port.succ)).execute
          (Function.update memory (entries 0).address
            (entries 0).value)).result = result
      exact ih (entries := fun port => entries port.succ)
        (memory := Function.update memory (entries 0).address (entries 0).value)

theorem writeFin_memory_of_ne {Result : Type} (result : Result)
    (degree : ℕ) (entries : Fin degree → WriteEntry wordBits)
    (memory : FiniteMemory wordBits) (address : CellProbe.Address wordBits)
    (different : ∀ port, (entries port).address ≠ address) :
    ((writeFin result degree entries).execute memory).memory address = memory address := by
  induction degree generalizing memory with
  | zero => rfl
  | succ degree ih =>
      change
        ((writeFin result degree (fun port => entries port.succ)).execute
          (Function.update memory (entries 0).address
            (entries 0).value)).memory address = memory address
      rw [ih (entries := fun port => entries port.succ)
        (memory := Function.update memory (entries 0).address
          (entries 0).value)]
      · exact Function.update_of_ne
          (fun equality => different 0 equality.symm)
          (entries 0).value memory
      · intro port
        exact different port.succ

theorem writeFin_memory_at {Result : Type} (result : Result)
    (degree : ℕ) (entries : Fin degree → WriteEntry wordBits)
    (injective : Function.Injective (fun port => (entries port).address))
    (memory : FiniteMemory wordBits) (port : Fin degree) :
    ((writeFin result degree entries).execute memory).memory
        (entries port).address = (entries port).value := by
  induction degree generalizing memory with
  | zero => exact Fin.elim0 port
  | succ degree ih =>
      refine Fin.cases ?_ (fun tail => ?_) port
      · change
          ((writeFin result degree (fun port => entries port.succ)).execute
            (Function.update memory (entries 0).address
              (entries 0).value)).memory (entries 0).address =
            (entries 0).value
        rw [writeFin_memory_of_ne]
        · exact Function.update_self _ _ _
        · intro later equality
          exact (Fin.succ_ne_zero later)
            (injective equality)
      · change
          ((writeFin result degree (fun port => entries port.succ)).execute
            (Function.update memory (entries 0).address
              (entries 0).value)).memory
                (entries tail.succ).address =
            (entries tail.succ).value
        apply ih (entries := fun p => entries p.succ)
          (memory := Function.update memory (entries 0).address
            (entries 0).value)
        intro left right equality
        exact Fin.succ_injective _ (injective equality)

noncomputable def edgeEntry
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (fresh : Fin maxNodes)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius)
    (port : Fin degree) : WriteEntry wordBits :=
  { address := packing.address (.nodeEdge fresh port)
    value := packing.offsetWord
      (resolveTarget fresh view (action.target port)) }

noncomputable def writeAction
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (fresh : Fin maxNodes)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius) :
    UpdateProgram wordBits
      (LocatedNeighborhood workLabelCount maxNodes degree radius ×
        Action (Fin stateCount) (Fin workLabelCount) degree radius)
      0 (finBudget 1 degree + 2) :=
  .write (packing.address .state) (packing.stateWord action.nextState) <|
    .write (packing.address (.nodeLabel fresh))
      (packing.labelWord (some action.newLabel)) <|
      writeFin (view, action) degree
        (edgeEntry packing fresh view action)

theorem edgeEntry_address_injective
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (fresh : Fin maxNodes)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius) :
    Function.Injective
      (fun port => (edgeEntry packing fresh view action port).address) := by
  intro left right equality
  have logical := packing.address_injective equality
  injection logical

theorem writeAction_memory_state
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (memory : FiniteMemory wordBits) (fresh : Fin maxNodes)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius) :
    ((writeAction packing fresh view action).execute memory).memory
        (packing.address .state) = packing.stateWord action.nextState := by
  rw [writeAction, UpdateProgram.execute, UpdateProgram.execute]
  rw [writeFin_memory_of_ne]
  · have state_ne :
        packing.address (.state : LogicalAddress maxNodes degree) ≠
          packing.address (.nodeLabel fresh) := by
        intro equality
        have logical := packing.address_injective equality
        contradiction
    rw [Function.update_of_ne state_ne]
    exact Function.update_self
        (packing.address (.state : LogicalAddress maxNodes degree))
        (packing.stateWord action.nextState) memory
  · intro port equality
    have logical := packing.address_injective equality
    contradiction

theorem writeAction_memory_label
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (memory : FiniteMemory wordBits) (fresh node : Fin maxNodes)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius) :
    ((writeAction packing fresh view action).execute memory).memory
        (packing.address (.nodeLabel node)) =
      if node = fresh then packing.labelWord (some action.newLabel)
      else memory (packing.address (.nodeLabel node)) := by
  rw [writeAction, UpdateProgram.execute, UpdateProgram.execute]
  rw [writeFin_memory_of_ne]
  · by_cases same : node = fresh
    · subst node
      simp
    · have label_ne :
          packing.address (.nodeLabel node) ≠
            packing.address (.nodeLabel fresh) := by
        intro equality
        have logical := packing.address_injective equality
        injection logical with equality
        exact same equality
      have state_ne :
          packing.address (.nodeLabel node) ≠ packing.address .state := by
        intro equality
        have logical := packing.address_injective equality
        contradiction
      rw [Function.update_of_ne label_ne,
        Function.update_of_ne state_ne]
      simp [same]
  · intro port equality
    have logical := packing.address_injective equality
    contradiction

theorem writeAction_memory_edge
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (memory : FiniteMemory wordBits) (fresh node : Fin maxNodes)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius)
    (port : Fin degree) :
    ((writeAction packing fresh view action).execute memory).memory
        (packing.address (.nodeEdge node port)) =
      if node = fresh then
        packing.offsetWord (resolveTarget fresh view (action.target port))
      else memory (packing.address (.nodeEdge node port)) := by
  change
    ((writeFin (view, action) degree
      (edgeEntry packing fresh view action)).execute
        (Function.update
          (Function.update memory
            (packing.address (.state : LogicalAddress maxNodes degree))
            (packing.stateWord action.nextState))
          (packing.address (.nodeLabel fresh))
          (packing.labelWord (some action.newLabel)))).memory
            (packing.address (.nodeEdge node port)) = _
  by_cases same : node = fresh
  · subst node
    rw [if_pos rfl]
    change
      ((writeFin (view, action) degree
        (edgeEntry packing fresh view action)).execute
          (Function.update
            (Function.update memory
              (packing.address (.state : LogicalAddress maxNodes degree))
              (packing.stateWord action.nextState))
            (packing.address (.nodeLabel fresh))
            (packing.labelWord (some action.newLabel)))).memory
              (edgeEntry packing fresh view action port).address =
        (edgeEntry packing fresh view action port).value
    exact writeFin_memory_at (view, action) degree
      (edgeEntry packing fresh view action)
      (edgeEntry_address_injective packing fresh view action) _ port
  · rw [writeFin_memory_of_ne]
    · have label_ne :
          packing.address (.nodeEdge node port) ≠
            packing.address (.nodeLabel fresh) := by
        intro equality
        have logical := packing.address_injective equality
        contradiction
      have state_ne :
          packing.address (.nodeEdge node port) ≠ packing.address .state := by
        intro equality
        have logical := packing.address_injective equality
        contradiction
      rw [Function.update_of_ne label_ne,
        Function.update_of_ne state_ne]
      simp [same]
    · intro later equality
      have logical := packing.address_injective equality
      injection logical with nodeEquality portEquality
      exact same nodeEquality.symm

theorem writeAction_represents
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (memory : FiniteMemory wordBits)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (room : graph.count < maxNodes)
    (represents : GraphPacking.Represents packing memory graph)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius) :
    GraphPacking.Represents packing
      ((writeAction packing ⟨graph.count, room⟩ view action).execute memory).memory
      (graph.appendAction room view action) := by
  intro logical
  cases logical with
  | state =>
      rw [writeAction_memory_state]
      rfl
  | nodeLabel node =>
      rw [writeAction_memory_label]
      by_cases same : node = ⟨graph.count, room⟩
      · subst node
        simp [GraphPacking.graphWord, StableGraph.appendAction]
      · rw [represents (.nodeLabel node)]
        simp [GraphPacking.graphWord, StableGraph.appendAction, same]
  | nodeEdge node port =>
      rw [writeAction_memory_edge]
      by_cases same : node = ⟨graph.count, room⟩
      · subst node
        simp [GraphPacking.graphWord, StableGraph.appendAction]
      · rw [represents (.nodeEdge node port)]
        simp [GraphPacking.graphWord, StableGraph.appendAction, same]

def reindexUpdate {Result : Type} {reads reads' writes writes' : ℕ}
    (readEq : reads = reads') (writeEq : writes = writes')
    (program : UpdateProgram wordBits Result reads writes) :
    UpdateProgram wordBits Result reads' writes' := by
  cases readEq
  cases writeEq
  exact program

@[simp] theorem reindexUpdate_execute {Result : Type}
    {reads reads' writes writes' : ℕ}
    (readEq : reads = reads') (writeEq : writes = writes')
    (program : UpdateProgram wordBits Result reads writes)
    (memory : FiniteMemory wordBits) :
    (reindexUpdate readEq writeEq program).execute memory =
      program.execute memory := by
  cases readEq
  cases writeEq
  rfl

theorem compiledRoot_eq
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (room : graph.count < maxNodes) :
    (⟨graph.count - 1,
      (Nat.pred_lt (Nat.ne_of_gt graph.count_pos)).trans room⟩ :
        Fin maxNodes) = graph.root := by
  apply Fin.ext
  rfl

noncomputable def compileStep
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (count : ℕ) (countPos : 0 < count) (room : count < maxNodes)
    (symbol : Terminal) :
    UpdateProgram wordBits
      (LocatedNeighborhood workLabelCount maxNodes degree radius ×
        Action (Fin stateCount) (Fin workLabelCount) degree radius)
      (viewBudget degree radius + 1) (finBudget 1 degree + 2) :=
  let root : Fin maxNodes :=
    ⟨count - 1, (Nat.pred_lt (Nat.ne_of_gt countPos)).trans room⟩
  let fresh : Fin maxNodes := ⟨count, room⟩
  reindexUpdate (Nat.zero_add _) (Nat.add_zero _) <|
    (UpdateProgram.ofRead
      (readStateAndView automaton packing dummyAddress root)).bind fun observed =>
        let action := automaton.transition observed.1 symbol observed.2.erase
        writeAction packing fresh observed.2 action

theorem finBudget_one (degree : ℕ) : finBudget 1 degree = degree := by
  rw [finBudget_eq_mul]
  simp

theorem compileStep_read_count
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (count : ℕ) (countPos : 0 < count) (room : count < maxNodes)
    (symbol : Terminal) (memory : FiniteMemory wordBits) :
    ((compileStep automaton packing dummyAddress count countPos room symbol).execute
      memory).readTrace.length = viewBudget degree radius + 1 :=
  UpdateProgram.execute_readTrace_length _ _

theorem compileStep_write_count
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (count : ℕ) (countPos : 0 < count) (room : count < maxNodes)
    (symbol : Terminal) (memory : FiniteMemory wordBits) :
    ((compileStep automaton packing dummyAddress count countPos room symbol).execute
      memory).writes.length = degree + 2 := by
  rw [UpdateProgram.execute_writes_length, finBudget_one]

theorem compileStep_result_correct
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (memory : FiniteMemory wordBits)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (room : graph.count < maxNodes)
    (represents : GraphPacking.Represents packing memory graph)
    (symbol : Terminal) :
    let view := graph.locatedView radius graph.root
    let action := automaton.transition graph.control symbol view.erase
    ((compileStep automaton packing dummyAddress graph.count graph.count_pos room symbol).execute
      memory).result = (view, action) := by
  dsimp only
  rw [compileStep, reindexUpdate_execute, UpdateProgram.bind_execute_result,
    UpdateProgram.ofRead_execute_result, UpdateProgram.ofRead_execute_memory,
    compiledRoot_eq graph room,
    readStateAndView_correct automaton packing dummyAddress memory graph represents]
  rw [writeAction, UpdateProgram.execute, UpdateProgram.execute,
    writeFin_execute_result]

theorem compileStep_preserves_representation
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (memory : FiniteMemory wordBits)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (room : graph.count < maxNodes)
    (represents : GraphPacking.Represents packing memory graph)
    (symbol : Terminal) :
    let view := graph.locatedView radius graph.root
    let action := automaton.transition graph.control symbol view.erase
    GraphPacking.Represents packing
      ((compileStep automaton packing dummyAddress graph.count graph.count_pos room symbol).execute
        memory).memory
      (graph.appendAction room view action) := by
  dsimp only
  rw [compileStep, reindexUpdate_execute, UpdateProgram.bind_execute_memory,
    UpdateProgram.ofRead_execute_result, UpdateProgram.ofRead_execute_memory,
    compiledRoot_eq graph room,
    readStateAndView_correct automaton packing dummyAddress memory graph represents]
  exact writeAction_represents packing memory graph room represents _ _

end StepCompiler

end PegSeparation.Reduction.SCACompiler
