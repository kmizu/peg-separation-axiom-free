import PegSeparation.CFLNotPEG.Reduction.SCABisimulation
import PegSeparation.CFLNotPEG.Reduction.HardMultiphase


namespace PegSeparation.Reduction.SCAQueryCompiler

open PegSeparation.Scaffolding
open PegSeparation.CellProbe
open PegSeparation.Reduction.SCAToCellProbe
open PegSeparation.Reduction.SCACompiler
open PegSeparation.Reduction.SCACompiler.StableGraph
open PegSeparation.Reduction.SCACompiler.ViewCompiler
open PegSeparation.Reduction.SCABisimulation
open PegSeparation.Reduction.HardMultiphase
open PegSeparation.Witness.HardSlice

variable {Terminal : Type}
variable {wordBits maxNodes stateCount workLabelCount degree radius : ℕ}

def emptyRecord : AbsoluteRecord workLabelCount maxNodes degree :=
  { label := none, edge := fun _ => none }

structure LocalOverlay (stateCount workLabelCount maxNodes degree : ℕ) where
  base : ℕ
  count : ℕ
  base_le_count : base ≤ count
  count_pos : 0 < count
  count_le : count ≤ maxNodes
  control : Fin stateCount
  records : Fin maxNodes → AbsoluteRecord workLabelCount maxNodes degree

namespace LocalOverlay

def root (overlay : LocalOverlay stateCount workLabelCount maxNodes degree) :
    Fin maxNodes :=
  ⟨overlay.count - 1,
    (Nat.pred_lt (Nat.ne_of_gt overlay.count_pos)).trans_le overlay.count_le⟩

def initial (count : ℕ) (countPos : 0 < count) (countLe : count ≤ maxNodes)
    (control : Fin stateCount) :
    LocalOverlay stateCount workLabelCount maxNodes degree :=
  { base := count
    count := count
    base_le_count := Nat.le_refl _
    count_pos := countPos
    count_le := countLe
    control := control
    records := fun _ => emptyRecord }

noncomputable def semanticGraph
    (persistent : StableGraph stateCount workLabelCount maxNodes degree)
    (overlay : LocalOverlay stateCount workLabelCount maxNodes degree) :
    StableGraph stateCount workLabelCount maxNodes degree :=
  { control := overlay.control
    count := overlay.count
    count_pos := overlay.count_pos
    count_le := overlay.count_le
    label := fun node =>
      if node.val < overlay.base then persistent.label node
      else (overlay.records node).label
    edge := fun node port =>
      if node.val < overlay.base then persistent.edge node port
      else (overlay.records node).edge port }

theorem semanticGraph_root
    (persistent : StableGraph stateCount workLabelCount maxNodes degree)
    (overlay : LocalOverlay stateCount workLabelCount maxNodes degree) :
    (overlay.semanticGraph persistent).root = overlay.root := by
  apply Fin.ext
  rfl

noncomputable def append
    (overlay : LocalOverlay stateCount workLabelCount maxNodes degree)
    (room : overlay.count < maxNodes)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius) :
    LocalOverlay stateCount workLabelCount maxNodes degree :=
  let fresh : Fin maxNodes := ⟨overlay.count, room⟩
  { base := overlay.base
    count := overlay.count + 1
    base_le_count := overlay.base_le_count.trans (Nat.le_succ _)
    count_pos := Nat.succ_pos _
    count_le := room
    control := action.nextState
    records := Function.update overlay.records fresh
      { label := some action.newLabel
        edge := fun port => resolveTarget fresh view (action.target port) } }

@[simp] theorem append_count
    (overlay : LocalOverlay stateCount workLabelCount maxNodes degree)
    (room : overlay.count < maxNodes)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius) :
    (overlay.append room view action).count = overlay.count + 1 := rfl

theorem stableGraph_ext
    {left right : StableGraph stateCount workLabelCount maxNodes degree}
    (control : left.control = right.control)
    (count : left.count = right.count)
    (label : left.label = right.label)
    (edge : left.edge = right.edge) : left = right := by
  cases left
  cases right
  simp_all

theorem semanticGraph_append
    (persistent : StableGraph stateCount workLabelCount maxNodes degree)
    (overlay : LocalOverlay stateCount workLabelCount maxNodes degree)
    (room : overlay.count < maxNodes)
    (view : LocatedNeighborhood workLabelCount maxNodes degree radius)
    (action : Action (Fin stateCount) (Fin workLabelCount) degree radius) :
    (overlay.append room view action).semanticGraph persistent =
      (overlay.semanticGraph persistent).appendAction room view action := by
  apply stableGraph_ext
  · rfl
  · rfl
  · funext node
    by_cases same : node = (⟨overlay.count, room⟩ : Fin maxNodes)
    · subst node
      have notPersistent : ¬ overlay.count < overlay.base :=
        Nat.not_lt_of_ge overlay.base_le_count
      simp [LocalOverlay.append, LocalOverlay.semanticGraph,
        StableGraph.appendAction, notPersistent]
    · by_cases persistentNode : node.val < overlay.base
      · simp [LocalOverlay.append, LocalOverlay.semanticGraph,
          StableGraph.appendAction, persistentNode, same]
      · simp [LocalOverlay.append, LocalOverlay.semanticGraph,
          StableGraph.appendAction, persistentNode, same]
  · funext node port
    by_cases same : node = (⟨overlay.count, room⟩ : Fin maxNodes)
    · subst node
      have notPersistent : ¬ overlay.count < overlay.base :=
        Nat.not_lt_of_ge overlay.base_le_count
      simp [LocalOverlay.append, LocalOverlay.semanticGraph,
        StableGraph.appendAction, notPersistent]
    · by_cases persistentNode : node.val < overlay.base
      · simp [LocalOverlay.append, LocalOverlay.semanticGraph,
          StableGraph.appendAction, persistentNode, same]
      · simp [LocalOverlay.append, LocalOverlay.semanticGraph,
          StableGraph.appendAction, persistentNode, same]

end LocalOverlay

noncomputable def initialSemanticCorrespondence
    {persistent : StableGraph stateCount workLabelCount maxNodes degree}
    {configuration : Fin stateCount × Scaffold (Fin workLabelCount) degree}
    (relation : ConfigurationCorresponds persistent configuration) :
    ConfigurationCorresponds
      ((LocalOverlay.initial (workLabelCount := workLabelCount)
        (degree := degree) persistent.count persistent.count_pos
          persistent.count_le persistent.control).semanticGraph persistent)
      configuration := by
  let overlay := LocalOverlay.initial (workLabelCount := workLabelCount)
    (degree := degree) persistent.count persistent.count_pos
      persistent.count_le persistent.control
  let graph := overlay.semanticGraph persistent
  refine
    { control_eq := relation.control_eq
      scaffold :=
        { locate := relation.scaffold.locate
          root := ?_
          allocated := ?_
          record_eq := ?_ } }
  · rw [relation.scaffold.root]
    apply congrArg some
    apply Fin.ext
    rfl
  · intro position node located
    exact relation.scaffold.allocated position node located
  · intro position
    rw [relation.scaffold.record_eq position]
    cases located : relation.scaffold.locate position with
    | none => rfl
    | some node =>
        have allocated := relation.scaffold.allocated position node located
        simp only [Option.map_some]
        apply congrArg some
        apply AbsoluteRecord.ext
        · simp [graph, overlay, LocalOverlay.semanticGraph,
            LocalOverlay.initial, StableGraph.record, allocated]
        · funext port
          simp [graph, overlay, LocalOverlay.semanticGraph,
            LocalOverlay.initial, StableGraph.record, allocated]


noncomputable def readOverlayRecord
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (overlay : LocalOverlay stateCount workLabelCount maxNodes degree)
    (node : Fin maxNodes) :
    ReadProgram wordBits (AbsoluteRecord workLabelCount maxNodes degree)
      (degree + 1) :=
  if persistent : node.val < overlay.base then
    GraphPacking.readRecordFixed packing node
  else
    ReadProgram.pad dummyAddress (overlay.records node) (degree + 1)

theorem readOverlayRecord_correct
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (memory : FiniteMemory wordBits)
    (persistent : StableGraph stateCount workLabelCount maxNodes degree)
    (represents : GraphPacking.Represents packing memory persistent)
    (overlay : LocalOverlay stateCount workLabelCount maxNodes degree)
    (node : Fin maxNodes) :
    ((readOverlayRecord packing dummyAddress overlay node).execute memory).result =
      (overlay.semanticGraph persistent).record node := by
  by_cases stored : node.val < overlay.base
  · rw [readOverlayRecord, dif_pos stored,
      GraphPacking.readRecordFixed_correct packing memory persistent
        represents node]
    apply AbsoluteRecord.ext
    · simp [LocalOverlay.semanticGraph, StableGraph.record, stored]
    · funext port
      simp [LocalOverlay.semanticGraph, StableGraph.record, stored]
  · rw [readOverlayRecord, dif_neg stored,
      ReadProgram.pad_execute_result]
    apply AbsoluteRecord.ext
    · simp [LocalOverlay.semanticGraph, StableGraph.record, stored]
    · funext port
      simp [LocalOverlay.semanticGraph, StableGraph.record, stored]

noncomputable def compileOverlayView
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (overlay : LocalOverlay stateCount workLabelCount maxNodes degree) :
    (viewRadius : ℕ) → Option (Fin maxNodes) →
      ReadProgram wordBits
        (LocatedChild workLabelCount maxNodes degree viewRadius)
        (viewBudget degree viewRadius)
  | viewRadius, none =>
      ReadProgram.pad dummyAddress .missing (viewBudget degree viewRadius)
  | 0, some node =>
      (readOverlayRecord packing dummyAddress overlay node).map fun record =>
        .present (.leaf node record.label)
  | viewRadius + 1, some node =>
      (readOverlayRecord packing dummyAddress overlay node).bind fun record =>
        (traverseFin degree (fun port =>
          compileOverlayView packing dummyAddress overlay viewRadius
            (record.edge port))).map fun children =>
              .present (.branch node record.label children)

theorem compileOverlayView_correct
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (memory : FiniteMemory wordBits)
    (persistent : StableGraph stateCount workLabelCount maxNodes degree)
    (represents : GraphPacking.Represents packing memory persistent)
    (overlay : LocalOverlay stateCount workLabelCount maxNodes degree)
    (viewRadius : ℕ) (cursor : Option (Fin maxNodes)) :
    ((compileOverlayView packing dummyAddress overlay viewRadius cursor).execute
      memory).result =
        semanticView (overlay.semanticGraph persistent) viewRadius cursor := by
  induction viewRadius generalizing cursor with
  | zero =>
      cases cursor with
      | none =>
          simp [compileOverlayView, semanticView,
            ReadProgram.pad_execute_result]
      | some node =>
          change
            (((readOverlayRecord packing dummyAddress overlay node).map
              fun record => LocatedChild.present
                (.leaf node record.label)).execute memory).result = _
          rw [ReadProgram.map_execute_result,
            readOverlayRecord_correct packing dummyAddress memory persistent
              represents overlay node]
          rfl
  | succ viewRadius ih =>
      cases cursor with
      | none =>
          simp [compileOverlayView, semanticView,
            ReadProgram.pad_execute_result]
      | some node =>
          change
            (((readOverlayRecord packing dummyAddress overlay node).bind
              fun record =>
                (traverseFin degree (fun port =>
                  compileOverlayView packing dummyAddress overlay viewRadius
                    (record.edge port))).map fun children =>
                      LocatedChild.present
                        (.branch node record.label children)).execute
                          memory).result = _
          rw [ReadProgram.bind_execute_result,
            readOverlayRecord_correct packing dummyAddress memory persistent
              represents overlay node,
            ReadProgram.map_execute_result,
            traverseFin_execute_result]
          simp only [semanticView, StableGraph.locatedView]
          congr 3
          funext port
          exact ih ((overlay.semanticGraph persistent).edge node port)


def suffixBudget (each : ℕ) : List Terminal → ℕ
  | [] => 0
  | _ :: rest => suffixBudget each rest + each

theorem suffixBudget_eq (each : ℕ) (symbols : List Terminal) :
    suffixBudget each symbols = symbols.length * each := by
  induction symbols with
  | nil => simp [suffixBudget]
  | cons symbol rest ih =>
      simp [suffixBudget, ih, Nat.succ_mul]

def reindexRead {Result : Type} {left right : ℕ}
    (equality : left = right)
    (program : ReadProgram wordBits Result left) :
    ReadProgram wordBits Result right :=
  cast (congrArg (ReadProgram wordBits Result) equality) program

@[simp] theorem reindexRead_execute {Result : Type} {left right : ℕ}
    (equality : left = right)
    (program : ReadProgram wordBits Result left)
    (memory : FiniteMemory wordBits) :
    (reindexRead equality program).execute memory = program.execute memory := by
  subst equality
  rfl

noncomputable def compileSuffix
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits) :
    (overlay : LocalOverlay stateCount workLabelCount maxNodes degree) →
    (symbols : List Terminal) →
    overlay.count + symbols.length ≤ maxNodes →
    ReadProgram wordBits
      (LocalOverlay stateCount workLabelCount maxNodes degree)
      (suffixBudget (viewBudget degree radius) symbols)
  | overlay, [], _ => .done overlay
  | overlay, symbol :: rest, space =>
      let room : overlay.count < maxNodes := by
        simp only [List.length_cons] at space
        omega
      reindexRead (by simp [suffixBudget]) <|
        (compileOverlayView packing dummyAddress overlay radius
          (some overlay.root)).bind fun loaded =>
            let view := loaded.getD overlay.root
            let action := automaton.transition overlay.control symbol view.erase
            let next := overlay.append room view action
            have nextSpace : next.count + rest.length ≤ maxNodes := by
              simp only [next, LocalOverlay.append_count]
              simp only [List.length_cons] at space
              omega
            compileSuffix automaton packing dummyAddress next rest nextSpace

theorem compileSuffix_probe_count
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (overlay : LocalOverlay stateCount workLabelCount maxNodes degree)
    (symbols : List Terminal)
    (space : overlay.count + symbols.length ≤ maxNodes)
    (memory : FiniteMemory wordBits) :
    ((compileSuffix automaton packing dummyAddress overlay symbols space).execute
      memory).trace.length = symbols.length * viewBudget degree radius := by
  rw [ReadProgram.execute_trace_length, suffixBudget_eq]

noncomputable def compileSuffixCorrespondence
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (memory : FiniteMemory wordBits)
    (persistent : StableGraph stateCount workLabelCount maxNodes degree)
    (represents : GraphPacking.Represents packing memory persistent)
    (overlay : LocalOverlay stateCount workLabelCount maxNodes degree)
    (configuration : Fin stateCount × Scaffold (Fin workLabelCount) degree)
    (relation : ConfigurationCorresponds
      (overlay.semanticGraph persistent) configuration)
    (symbols : List Terminal)
    (space : overlay.count + symbols.length ≤ maxNodes) :
    ConfigurationCorresponds
      (((compileSuffix automaton packing dummyAddress overlay symbols space).execute
        memory).result.semanticGraph persistent)
      (QueryOverlay.runFrom automaton configuration symbols) := by
  induction symbols generalizing overlay configuration with
  | nil =>
      change ConfigurationCorresponds
        (overlay.semanticGraph persistent) configuration
      exact relation
  | cons symbol rest ih =>
      let graph := overlay.semanticGraph persistent
      let room : overlay.count < maxNodes := by
        simp only [List.length_cons] at space
        omega
      have loadedResult :
          ((compileOverlayView packing dummyAddress overlay radius
            (some overlay.root)).execute memory).result =
            .present (graph.locatedView radius overlay.root) := by
        simpa [graph, semanticView] using
          compileOverlayView_correct packing dummyAddress memory persistent
            represents overlay radius (some overlay.root)
      let view := graph.locatedView radius overlay.root
      let action := automaton.transition overlay.control symbol view.erase
      let next := overlay.append room view action
      have nextSpace : next.count + rest.length ≤ maxNodes := by
        simp only [next, LocalOverlay.append_count]
        simp only [List.length_cons] at space
        omega
      have nextRelation : ConfigurationCorresponds
          (next.semanticGraph persistent)
          (automaton.step configuration symbol) := by
        rw [LocalOverlay.semanticGraph_append]
        have stepped := relation.step automaton room symbol
        have rootEquality : graph.root = overlay.root := by
          exact LocalOverlay.semanticGraph_root persistent overlay
        unfold SCABisimulation.stableStep at stepped
        change ConfigurationCorresponds
          (graph.appendAction room
            (graph.locatedView radius graph.root)
            (automaton.transition overlay.control symbol
              (graph.locatedView radius graph.root).erase))
          (automaton.step configuration symbol) at stepped
        rw [rootEquality] at stepped
        exact stepped
      have resultEquality :
          ((compileSuffix automaton packing dummyAddress overlay
            (symbol :: rest) space).execute memory).result =
          ((compileSuffix automaton packing dummyAddress next rest
            nextSpace).execute memory).result := by
        rw [compileSuffix, reindexRead_execute,
          ReadProgram.bind_execute_result, loadedResult]
        simp only [LocatedChild.getD]
        rfl
      simp only [QueryOverlay.runFrom]
      rw [resultEquality]
      exact ih next (automaton.step configuration symbol) nextRelation nextSpace


def queryBudget (degree radius : ℕ) (symbols : List Terminal) : ℕ :=
  suffixBudget (viewBudget degree radius) symbols + 1

theorem queryBudget_eq (degree radius : ℕ) (symbols : List Terminal) :
    queryBudget degree radius symbols =
      1 + symbols.length * viewBudget degree radius := by
  rw [queryBudget, suffixBudget_eq]
  omega

noncomputable def compileQuery
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (count : ℕ) (countPos : 0 < count) (countLe : count ≤ maxNodes)
    (symbols : List Terminal) (space : count + symbols.length ≤ maxNodes) :
    ReadProgram wordBits Bool (queryBudget degree radius symbols) :=
  reindexRead (by simp [queryBudget]) <|
    (ReadProgram.readCell (packing.address .state)).bind fun stateWord =>
      let control := SCACompiler.StepCompiler.decodeState
        automaton.initialState stateWord
      let overlay := LocalOverlay.initial (workLabelCount := workLabelCount)
        (degree := degree) count countPos countLe control
      (compileSuffix automaton packing dummyAddress overlay symbols (by
        simpa [overlay, LocalOverlay.initial] using space)).map fun finalOverlay =>
          decide (finalOverlay.control ∈ automaton.accepting)

theorem compileQuery_probe_count
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (count : ℕ) (countPos : 0 < count) (countLe : count ≤ maxNodes)
    (symbols : List Terminal) (space : count + symbols.length ≤ maxNodes)
    (memory : FiniteMemory wordBits) :
    ((compileQuery automaton packing dummyAddress count countPos countLe
      symbols space).execute memory).trace.length =
        1 + symbols.length * viewBudget degree radius := by
  rw [ReadProgram.execute_trace_length, queryBudget_eq]

theorem compileQuery_correct
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (memory : FiniteMemory wordBits)
    (persistent : StableGraph stateCount workLabelCount maxNodes degree)
    (represents : GraphPacking.Represents packing memory persistent)
    (configuration : Fin stateCount × Scaffold (Fin workLabelCount) degree)
    (relation : ConfigurationCorresponds persistent configuration)
    (symbols : List Terminal)
    (space : persistent.count + symbols.length ≤ maxNodes) :
    ((compileQuery automaton packing dummyAddress persistent.count
      persistent.count_pos persistent.count_le symbols space).execute
        memory).result =
      decide ((QueryOverlay.runFrom automaton configuration symbols).1 ∈
        automaton.accepting) := by
  let initial := LocalOverlay.initial (workLabelCount := workLabelCount)
    (degree := degree) persistent.count persistent.count_pos
      persistent.count_le persistent.control
  have initialRelation : ConfigurationCorresponds
      (initial.semanticGraph persistent) configuration := by
    exact initialSemanticCorrespondence relation
  have finalRelation := compileSuffixCorrespondence automaton packing
    dummyAddress memory persistent represents initial configuration
      initialRelation symbols (by simpa [initial, LocalOverlay.initial] using space)
  have controlEquality :
      ((compileSuffix automaton packing dummyAddress initial symbols (by
        simpa [initial, LocalOverlay.initial] using space)).execute
          memory).result.control =
        (QueryOverlay.runFrom automaton configuration symbols).1 := by
    exact finalRelation.control_eq
  have stateRead :
      memory (packing.address (.state : LogicalAddress maxNodes degree)) =
        packing.stateWord persistent.control := by
    exact represents .state
  rw [compileQuery, reindexRead_execute, ReadProgram.bind_execute_result,
    ReadProgram.readCell_result, stateRead,
    SCACompiler.StepCompiler.decodeState_stateWord,
    ReadProgram.map_execute_result]
  exact congrArg (fun state => decide (state ∈ automaton.accepting))
    controlEquality


theorem compileHardQuery_probe_count
    {n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (count : ℕ) (countPos : 0 < count) (countLe : count ≤ maxNodes)
    (q : Fin (rowCount n))
    (space : count + (hardQuerySuffix q).length ≤ maxNodes)
    (memory : FiniteMemory wordBits) :
    ((compileQuery automaton packing dummyAddress count countPos countLe
      (hardQuerySuffix q) space).execute memory).trace.length =
        1 + (keyWidth n + 1) * viewBudget degree radius := by
  rw [compileQuery_probe_count, hardQuerySuffix_length]

theorem hardQuery_budget_le_scaled
    {n : ℕ} (q : Fin (rowCount n)) :
    queryBudget degree radius (hardQuerySuffix q) ≤
      (2 * perSymbolBudget degree radius) *
        (Nat.clog 2 (n + 1) + 1) := by
  have viewLe : viewBudget degree radius ≤
      perSymbolBudget degree radius := by
    rw [viewBudget_eq]
    unfold perSymbolBudget
    omega
  have budgetPos : 0 < perSymbolBudget degree radius := by
    unfold perSymbolBudget
    omega
  have lengthLe : (hardQuerySuffix q).length + 1 ≤
      2 * (Nat.clog 2 (n + 1) + 1) := by
    rw [hardQuerySuffix_length, keyWidth_eq_indexWidth]
    have := hardQueryLength_le n
    unfold hardQueryLength at this
    omega
  rw [queryBudget_eq]
  calc
    1 + (hardQuerySuffix q).length * viewBudget degree radius ≤
        perSymbolBudget degree radius +
          (hardQuerySuffix q).length * perSymbolBudget degree radius := by
      exact Nat.add_le_add (by omega)
        (Nat.mul_le_mul_left _ viewLe)
    _ = ((hardQuerySuffix q).length + 1) *
        perSymbolBudget degree radius := by ring
    _ ≤ (2 * (Nat.clog 2 (n + 1) + 1)) *
        perSymbolBudget degree radius :=
      Nat.mul_le_mul_right _ lengthLe
    _ = (2 * perSymbolBudget degree radius) *
        (Nat.clog 2 (n + 1) + 1) := by ring

theorem compileHardQuery_correct
    {n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (decidesC : ∀ word, automaton.Accepts word ↔
      word ∈ PegSeparation.Witness.LanguageCFG.C)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (memory : FiniteMemory wordBits)
    (S : Matrix n) (X : Vector n) (q : Fin (rowCount n))
    (persistent : StableGraph stateCount workLabelCount maxNodes degree)
    (represents : GraphPacking.Represents packing memory persistent)
    (relation : ConfigurationCorresponds persistent
      (QueryOverlay.runFrom automaton (automaton.run (hardPhaseI S))
        (hardUpdates X)))
    (space : persistent.count + (hardQuerySuffix q).length ≤ maxNodes) :
    ((compileQuery automaton packing dummyAddress persistent.count
      persistent.count_pos persistent.count_le (hardQuerySuffix q) space).execute
        memory).result =
      decide (vectorInnerProduct (S q) X = 1) := by
  let persistentConfiguration :=
    QueryOverlay.runFrom automaton (automaton.run (hardPhaseI S))
      (hardUpdates X)
  have compiled := compileQuery_correct automaton packing dummyAddress memory
    persistent represents persistentConfiguration relation (hardQuerySuffix q)
      space
  rw [compiled]
  have readOnly := QueryOverlay.readOnly_exact automaton
    persistentConfiguration (hardQuerySuffix q)
  have wholeRun := hardMultiphase_execution_exact automaton S X q
  dsimp only at wholeRun
  have executionEquality :
      QueryOverlay.runFrom automaton persistentConfiguration
          (hardQuerySuffix q) =
        automaton.run (hardWord S X q) :=
    readOnly.symm.trans wholeRun
  have answerIff :
      (QueryOverlay.runFrom automaton persistentConfiguration
          (hardQuerySuffix q)).1 ∈ automaton.accepting ↔
        vectorInnerProduct (S q) X = 1 := by
    rw [executionEquality]
    simpa [Automaton.Accepts, hardWord_eq_parts] using
      accepts_parts_iff_innerProduct automaton decidesC S X q
  by_cases accepted :
      (QueryOverlay.runFrom automaton persistentConfiguration
        (hardQuerySuffix q)).1 ∈ automaton.accepting
  · have product := answerIff.mp accepted
    simp [accepted, product]
  · have product : vectorInnerProduct (S q) X ≠ 1 := by
      exact fun equality => accepted (answerIff.mpr equality)
    simp [accepted, product]

end PegSeparation.Reduction.SCAQueryCompiler
