import PegSeparation.Common.Model.Scaffolding
import PegSeparation.CFLNotPEG.Model.Communication


namespace PegSeparation.Reduction.SCAToCellProbe

open PegSeparation.Scaffolding
open PegSeparation.CellProbe


abbrev Configuration (stateCount workLabelCount degree : ℕ) :=
  Fin stateCount × Scaffold (Fin workLabelCount) degree

structure QueryOverlay (stateCount workLabelCount degree : ℕ) where
  persistent : Configuration stateCount workLabelCount degree
  localNodes : List (Node (Fin workLabelCount) degree)
  control : Fin stateCount

namespace QueryOverlay

variable {Terminal : Type}
  {stateCount workLabelCount degree radius : ℕ}

def scaffold (overlay : QueryOverlay stateCount workLabelCount degree) :
    Scaffold (Fin workLabelCount) degree :=
  match overlay.localNodes with
  | [] => overlay.persistent.2
  | top :: olderLocal =>
      { top := top
        older := olderLocal ++ overlay.persistent.2.nodes }

def materialize (overlay : QueryOverlay stateCount workLabelCount degree) :
    Configuration stateCount workLabelCount degree :=
  (overlay.control, overlay.scaffold)

def beginQuery
    (persistent : Configuration stateCount workLabelCount degree) :
    QueryOverlay stateCount workLabelCount degree :=
  { persistent := persistent
    localNodes := []
    control := persistent.1 }

@[simp] theorem materialize_beginQuery
    (persistent : Configuration stateCount workLabelCount degree) :
    (beginQuery persistent).materialize = persistent := by
  cases persistent
  rfl

def step
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (overlay : QueryOverlay stateCount workLabelCount degree)
    (symbol : Terminal) : QueryOverlay stateCount workLabelCount degree :=
  let current := overlay.materialize
  let action := automaton.transition current.1 symbol
    (current.2.topNeighborhood radius)
  let extended := Scaffolding.Automaton.extendScaffold current.2 action
  { persistent := overlay.persistent
    localNodes := extended.top :: overlay.localNodes
    control := action.nextState }

@[simp] theorem step_persistent
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (overlay : QueryOverlay stateCount workLabelCount degree)
    (symbol : Terminal) :
    (overlay.step automaton symbol).persistent = overlay.persistent := rfl

theorem materialize_step
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (overlay : QueryOverlay stateCount workLabelCount degree)
    (symbol : Terminal) :
    (overlay.step automaton symbol).materialize =
      automaton.step overlay.materialize symbol := by
  cases h : overlay.localNodes with
  | nil =>
      simp [step, materialize, scaffold, h,
        Scaffolding.Automaton.step,
        Scaffolding.Automaton.extendScaffold,
        Scaffolding.Scaffold.nodes]
  | cons top olderLocal =>
      simp [step, materialize, scaffold, h,
        Scaffolding.Automaton.step,
        Scaffolding.Automaton.extendScaffold,
        Scaffolding.Scaffold.nodes]

def run
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius) :
    QueryOverlay stateCount workLabelCount degree → List Terminal →
      QueryOverlay stateCount workLabelCount degree
  | overlay, [] => overlay
  | overlay, symbol :: rest => run automaton (overlay.step automaton symbol) rest

def runFrom
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius) :
    Configuration stateCount workLabelCount degree → List Terminal →
      Configuration stateCount workLabelCount degree
  | configuration, [] => configuration
  | configuration, symbol :: rest =>
      runFrom automaton (automaton.step configuration symbol) rest

theorem runFrom_append
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (configuration : Configuration stateCount workLabelCount degree)
    (left right : List Terminal) :
    runFrom automaton configuration (left ++ right) =
      runFrom automaton (runFrom automaton configuration left) right := by
  induction left generalizing configuration with
  | nil => rfl
  | cons symbol rest ih =>
      exact ih (automaton.step configuration symbol)

theorem runFrom_eq_foldl
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (configuration : Configuration stateCount workLabelCount degree)
    (input : List Terminal) :
    runFrom automaton configuration input =
      input.foldl automaton.step configuration := by
  induction input generalizing configuration with
  | nil => rfl
  | cons symbol rest ih => exact ih (automaton.step configuration symbol)

theorem runFrom_initial
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (input : List Terminal) :
    runFrom automaton
        (automaton.initialState, Scaffolding.Automaton.initialScaffold) input =
      automaton.run input := by
  rw [runFrom_eq_foldl]
  rfl

@[simp] theorem run_persistent
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (overlay : QueryOverlay stateCount workLabelCount degree)
    (input : List Terminal) :
    (overlay.run automaton input).persistent = overlay.persistent := by
  induction input generalizing overlay with
  | nil => rfl
  | cons symbol rest ih =>
      exact (ih (overlay.step automaton symbol)).trans
        (step_persistent automaton overlay symbol)

theorem materialize_run
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (overlay : QueryOverlay stateCount workLabelCount degree)
    (input : List Terminal) :
    (overlay.run automaton input).materialize =
      runFrom automaton overlay.materialize input := by
  induction input generalizing overlay with
  | nil => rfl
  | cons symbol rest ih =>
      rw [run, runFrom, ih, materialize_step]

theorem readOnly_exact
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (persistent : Configuration stateCount workLabelCount degree)
    (querySuffix : List Terminal) :
    ((beginQuery persistent).run automaton querySuffix).materialize =
      runFrom automaton persistent querySuffix := by
  rw [materialize_run, materialize_beginQuery]

theorem readOnly_persistent_unchanged
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (persistent : Configuration stateCount workLabelCount degree)
    (querySuffix : List Terminal) :
    ((beginQuery persistent).run automaton querySuffix).persistent = persistent := by
  rw [run_persistent]
  rfl

theorem multiphase_execution_exact
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius)
    (phaseI updates querySuffix : List Terminal) :
    let persistent := runFrom automaton (automaton.run phaseI) updates
    ((beginQuery persistent).run automaton querySuffix).materialize =
      automaton.run (phaseI ++ updates ++ querySuffix) := by
  dsimp only
  rw [readOnly_exact]
  rw [← runFrom_initial automaton phaseI]
  rw [← runFrom_initial automaton (phaseI ++ updates ++ querySuffix)]
  rw [List.append_assoc, runFrom_append, runFrom_append]

end QueryOverlay


abbrev FiniteMemory (wordBits : ℕ) :=
  CellProbe.Address wordBits → CellProbe.Word wordBits

structure WriteEntry (wordBits : ℕ) where
  address : CellProbe.Address wordBits
  value : CellProbe.Word wordBits
  deriving DecidableEq

def replayWrites {wordBits : ℕ} :
    FiniteMemory wordBits → List (WriteEntry wordBits) → FiniteMemory wordBits
  | memory, [] => memory
  | memory, write :: rest =>
      replayWrites (Function.update memory write.address write.value) rest

def lastWritten {wordBits : ℕ} :
    List (WriteEntry wordBits) → CellProbe.Address wordBits →
      Option (CellProbe.Word wordBits)
  | [], _ => none
  | write :: rest, address =>
      match lastWritten rest address with
      | some value => some value
      | none => if write.address = address then some write.value else none

def readWithCache {wordBits : ℕ}
    (preinitialized : FiniteMemory wordBits)
    (writes : List (WriteEntry wordBits))
    (address : CellProbe.Address wordBits) : CellProbe.Word wordBits :=
  (lastWritten writes address).getD (preinitialized address)

theorem replayWrites_apply {wordBits : ℕ}
    (preinitialized : FiniteMemory wordBits)
    (writes : List (WriteEntry wordBits))
    (address : CellProbe.Address wordBits) :
    replayWrites preinitialized writes address =
      readWithCache preinitialized writes address := by
  induction writes generalizing preinitialized with
  | nil => rfl
  | cons write rest ih =>
      rw [replayWrites, ih]
      unfold readWithCache
      cases hlast : lastWritten rest address with
      | some value => simp [lastWritten, hlast]
      | none =>
          by_cases heq : write.address = address
          · subst address
            simp [lastWritten, hlast]
          · rw [Function.update_of_ne (fun equality => heq equality.symm)]
            simp [lastWritten, hlast, heq]

structure PreinitializedCache (wordBits : ℕ) where
  preinitialized : FiniteMemory wordBits
  writes : List (WriteEntry wordBits)

namespace PreinitializedCache

def memory {wordBits : ℕ} (cache : PreinitializedCache wordBits) :
    FiniteMemory wordBits :=
  replayWrites cache.preinitialized cache.writes

def read {wordBits : ℕ} (cache : PreinitializedCache wordBits)
    (address : CellProbe.Address wordBits) : CellProbe.Word wordBits :=
  readWithCache cache.preinitialized cache.writes address

theorem memory_eq_read {wordBits : ℕ} (cache : PreinitializedCache wordBits) :
    cache.memory = cache.read := by
  funext address
  exact replayWrites_apply cache.preinitialized cache.writes address

def append {wordBits : ℕ} (cache : PreinitializedCache wordBits)
    (later : List (WriteEntry wordBits)) : PreinitializedCache wordBits :=
  { preinitialized := cache.preinitialized
    writes := cache.writes ++ later }

@[simp] theorem append_preinitialized {wordBits : ℕ}
    (cache : PreinitializedCache wordBits) (later : List (WriteEntry wordBits)) :
    (cache.append later).preinitialized = cache.preinitialized := rfl

end PreinitializedCache


inductive ReadProgram (wordBits : ℕ) (Result : Type) : ℕ → Type
  | done (result : Result) : ReadProgram wordBits Result 0
  | probe {probes : ℕ} (address : CellProbe.Address wordBits)
      (next : CellProbe.Word wordBits → ReadProgram wordBits Result probes) :
      ReadProgram wordBits Result (probes + 1)

structure ReadExecution (wordBits : ℕ) (Result : Type) where
  result : Result
  trace : List (CellProbe.Address wordBits)

namespace ReadProgram

variable {wordBits : ℕ} {Result : Type}

def execute (memory : FiniteMemory wordBits) :
    {probes : ℕ} → ReadProgram wordBits Result probes →
      ReadExecution wordBits Result
  | _, .done result => { result := result, trace := [] }
  | _, .probe address next =>
      let continuation := execute memory (next (memory address))
      { result := continuation.result
        trace := address :: continuation.trace }

theorem execute_trace_length (memory : FiniteMemory wordBits)
    {probes : ℕ} (program : ReadProgram wordBits Result probes) :
    (program.execute memory).trace.length = probes := by
  induction program with
  | done => rfl
  | @probe probes address next ih =>
      simp only [execute, List.length_cons]
      rw [ih (memory address)]

theorem execute_cast {left right : ℕ} (equality : left = right)
    (program : ReadProgram wordBits Result left)
    (memory : FiniteMemory wordBits) :
    (execute memory (cast (congrArg (ReadProgram wordBits Result) equality) program)) =
      execute memory program := by
  subst equality
  rfl

def readCell (address : CellProbe.Address wordBits) :
    ReadProgram wordBits (CellProbe.Word wordBits) 1 :=
  .probe address (fun value => .done value)

@[simp] theorem readCell_result (memory : FiniteMemory wordBits)
    (address : CellProbe.Address wordBits) :
    ((readCell address).execute memory).result = memory address := rfl

def map {Other : Type} (transform : Result → Other) :
    {probes : ℕ} → ReadProgram wordBits Result probes →
      ReadProgram wordBits Other probes
  | _, .done result => .done (transform result)
  | _, .probe address next =>
      .probe address (fun value => map transform (next value))

def bind {Other : Type} {first second : ℕ}
    (program : ReadProgram wordBits Result first)
    (next : Result → ReadProgram wordBits Other second) :
    ReadProgram wordBits Other (second + first) :=
  match program with
  | .done result => next result
  | @ReadProgram.probe _ _ probes address continuation =>
      ReadProgram.probe address (fun value => bind (continuation value) next)

theorem bind_execute_result {Other : Type} {first second : ℕ}
    (memory : FiniteMemory wordBits)
    (program : ReadProgram wordBits Result first)
    (next : Result → ReadProgram wordBits Other second) :
    ((program.bind next).execute memory).result =
      ((next (program.execute memory).result).execute memory).result := by
  induction program with
  | done => rfl
  | @probe probes address continuation ih =>
      exact ih (memory address)

@[simp] theorem map_execute_result {Other : Type}
    (transform : Result → Other) (memory : FiniteMemory wordBits)
    {probes : ℕ} (program : ReadProgram wordBits Result probes) :
    ((program.map transform).execute memory).result =
      transform (program.execute memory).result := by
  induction program with
  | done => rfl
  | @probe probes address next ih =>
      exact ih (memory address)

def readCells : (addresses : List (CellProbe.Address wordBits)) →
    ReadProgram wordBits (List (CellProbe.Word wordBits)) addresses.length
  | [] => .done []
  | address :: rest =>
      .probe address (fun value => (readCells rest).map (value :: ·))

theorem readCells_result (memory : FiniteMemory wordBits)
    (addresses : List (CellProbe.Address wordBits)) :
    ((readCells addresses).execute memory).result = addresses.map memory := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
      change
        (((readCells rest).map (memory address :: ·)).execute memory).result =
          memory address :: List.map memory rest
      rw [map_execute_result, ih]

def pad (address : CellProbe.Address wordBits) (result : Result) :
    (probes : ℕ) → ReadProgram wordBits Result probes
  | 0 => .done result
  | probes + 1 => .probe address (fun _ => pad address result probes)

@[simp] theorem pad_execute_result (memory : FiniteMemory wordBits)
    (address : CellProbe.Address wordBits) (result : Result) (probes : ℕ) :
    ((pad address result probes).execute memory).result = result := by
  induction probes with
  | zero => rfl
  | succ probes ih => exact ih

def padAfter (address : CellProbe.Address wordBits) {probes : ℕ}
    (program : ReadProgram wordBits Result probes) (extra : ℕ) :
    ReadProgram wordBits Result (extra + probes) :=
  program.bind fun result => pad address result extra

@[simp] theorem padAfter_execute_result
    (memory : FiniteMemory wordBits)
    (address : CellProbe.Address wordBits) {probes : ℕ}
    (program : ReadProgram wordBits Result probes) (extra : ℕ) :
    ((padAfter address program extra).execute memory).result =
      (program.execute memory).result := by
  rw [padAfter, bind_execute_result, pad_execute_result]

def padTo (address : CellProbe.Address wordBits) {probes target : ℕ}
    (within : probes ≤ target)
    (program : ReadProgram wordBits Result probes) :
    ReadProgram wordBits Result target :=
  cast (congrArg (ReadProgram wordBits Result)
    (Nat.sub_add_cancel within))
    (padAfter address program (target - probes))

@[simp] theorem padTo_execute_result
    (memory : FiniteMemory wordBits)
    (address : CellProbe.Address wordBits) {probes target : ℕ}
    (within : probes ≤ target)
    (program : ReadProgram wordBits Result probes) :
    ((padTo address within program).execute memory).result =
      (program.execute memory).result := by
  unfold padTo
  rw [execute_cast (Nat.sub_add_cancel within)
    (padAfter address program (target - probes)) memory]
  exact padAfter_execute_result memory address program (target - probes)

def traversalBudget {Input : Type} (each : ℕ) : List Input → ℕ
  | [] => 0
  | _ :: rest => traversalBudget each rest + each

theorem traversalBudget_eq_length_mul {Input : Type} (each : ℕ)
    (inputs : List Input) :
    traversalBudget each inputs = inputs.length * each := by
  induction inputs with
  | nil => simp [traversalBudget]
  | cons input rest ih => simp [traversalBudget, ih, Nat.succ_mul]

def traverseFixed {Input Output : Type} {each : ℕ}
    (program : Input → ReadProgram wordBits Output each) :
    (inputs : List Input) →
      ReadProgram wordBits (List Output) (traversalBudget each inputs)
  | [] => .done []
  | input :: rest =>
      (program input).bind (fun output =>
        (traverseFixed program rest).map (output :: ·))

def toQueryTree {probes : ℕ} :
    ReadProgram wordBits Bool probes → CellProbe.QueryTree wordBits
  | .done answer => .answer answer
  | .probe address next =>
      .probe address (fun value => toQueryTree (next value))

theorem toQueryTree_run {probes : ℕ}
    (program : ReadProgram wordBits Bool probes)
    (memory : FiniteMemory wordBits) :
    program.toQueryTree.run memory =
      ((program.execute memory).result, (program.execute memory).trace) := by
  induction program with
  | done => rfl
  | @probe probes address next ih =>
      simp only [toQueryTree, CellProbe.QueryTree.run, execute]
      rw [ih (memory address)]

theorem toQueryTree_trace_length {probes : ℕ}
    (program : ReadProgram wordBits Bool probes)
    (memory : FiniteMemory wordBits) :
    (program.toQueryTree.run memory).2.length = probes := by
  rw [toQueryTree_run, execute_trace_length]

end ReadProgram

inductive UpdateProgram (wordBits : ℕ) (Result : Type) : ℕ → ℕ → Type
  | done (result : Result) : UpdateProgram wordBits Result 0 0
  | read {reads writes : ℕ} (address : CellProbe.Address wordBits)
      (next : CellProbe.Word wordBits →
        UpdateProgram wordBits Result reads writes) :
      UpdateProgram wordBits Result (reads + 1) writes
  | write {reads writes : ℕ} (address : CellProbe.Address wordBits)
      (value : CellProbe.Word wordBits)
      (next : UpdateProgram wordBits Result reads writes) :
      UpdateProgram wordBits Result reads (writes + 1)

structure UpdateExecution (wordBits : ℕ) (Result : Type) where
  result : Result
  memory : FiniteMemory wordBits
  readTrace : List (CellProbe.Address wordBits)
  writes : List (WriteEntry wordBits)

namespace UpdateProgram

variable {wordBits : ℕ} {Result : Type}

def execute (initial : FiniteMemory wordBits) :
    {reads writes : ℕ} → UpdateProgram wordBits Result reads writes →
      UpdateExecution wordBits Result
  | _, _, .done result =>
      { result := result, memory := initial, readTrace := [], writes := [] }
  | _, _, .read address next =>
      let continuation := execute initial (next (initial address))
      { continuation with readTrace := address :: continuation.readTrace }
  | _, _, .write address value next =>
      let updated := Function.update initial address value
      let continuation := execute updated next
      { continuation with
        writes := { address := address, value := value } :: continuation.writes }

def bind {Other : Type} {firstReads firstWrites secondReads secondWrites : ℕ}
    (program : UpdateProgram wordBits Result firstReads firstWrites)
    (next : Result →
      UpdateProgram wordBits Other secondReads secondWrites) :
    UpdateProgram wordBits Other
      (secondReads + firstReads) (secondWrites + firstWrites) :=
  match program with
  | .done result => next result
  | @UpdateProgram.read _ _ reads writes address continuation =>
      .read address (fun value => bind (continuation value) next)
  | @UpdateProgram.write _ _ reads writes address value continuation =>
      .write address value (bind continuation next)

def ofRead {reads : ℕ} : ReadProgram wordBits Result reads →
    UpdateProgram wordBits Result reads 0
  | .done result => .done result
  | .probe address next => .read address (fun value => ofRead (next value))

theorem ofRead_execute_result (initial : FiniteMemory wordBits)
    {reads : ℕ} (program : ReadProgram wordBits Result reads) :
    ((ofRead program).execute initial).result = (program.execute initial).result := by
  induction program with
  | done => rfl
  | @probe reads address next ih => exact ih (initial address)

theorem ofRead_execute_memory (initial : FiniteMemory wordBits)
    {reads : ℕ} (program : ReadProgram wordBits Result reads) :
    ((ofRead program).execute initial).memory = initial := by
  induction program with
  | done => rfl
  | @probe reads address next ih => exact ih (initial address)

theorem bind_execute_result {Other : Type}
    {firstReads firstWrites secondReads secondWrites : ℕ}
    (initial : FiniteMemory wordBits)
    (program : UpdateProgram wordBits Result firstReads firstWrites)
    (next : Result →
      UpdateProgram wordBits Other secondReads secondWrites) :
    ((program.bind next).execute initial).result =
      ((next (program.execute initial).result).execute
        (program.execute initial).memory).result := by
  induction program generalizing initial with
  | done => rfl
  | @read reads writes address continuation ih =>
      exact ih (initial address) initial
  | @write reads writes address value continuation ih =>
      exact ih (Function.update initial address value)

theorem bind_execute_memory {Other : Type}
    {firstReads firstWrites secondReads secondWrites : ℕ}
    (initial : FiniteMemory wordBits)
    (program : UpdateProgram wordBits Result firstReads firstWrites)
    (next : Result →
      UpdateProgram wordBits Other secondReads secondWrites) :
    ((program.bind next).execute initial).memory =
      ((next (program.execute initial).result).execute
        (program.execute initial).memory).memory := by
  induction program generalizing initial with
  | done => rfl
  | @read reads writes address continuation ih =>
      exact ih (initial address) initial
  | @write reads writes address value continuation ih =>
      exact ih (Function.update initial address value)

theorem execute_readTrace_length (initial : FiniteMemory wordBits)
    {reads writes : ℕ} (program : UpdateProgram wordBits Result reads writes) :
    (program.execute initial).readTrace.length = reads := by
  induction program generalizing initial with
  | done => rfl
  | @read reads writes address next ih =>
      simp only [execute, List.length_cons]
      rw [ih (initial address) initial]
  | @write reads writes address value next ih =>
      simp only [execute]
      exact ih (Function.update initial address value)

theorem execute_writes_length (initial : FiniteMemory wordBits)
    {reads writes : ℕ} (program : UpdateProgram wordBits Result reads writes) :
    (program.execute initial).writes.length = writes := by
  induction program generalizing initial with
  | done => rfl
  | @read reads writes address next ih =>
      simp only [execute]
      exact ih (initial address) initial
  | @write reads writes address value next ih =>
      simp only [execute, List.length_cons]
      rw [ih (Function.update initial address value)]

theorem execute_memory_eq_replay (initial : FiniteMemory wordBits)
    {reads writes : ℕ} (program : UpdateProgram wordBits Result reads writes) :
    (program.execute initial).memory =
      replayWrites initial (program.execute initial).writes := by
  induction program generalizing initial with
  | done => rfl
  | @read reads writes address next ih =>
      simp only [execute]
      exact ih (initial address) initial
  | @write reads writes address value next ih =>
      simp only [execute, replayWrites]
      exact ih (Function.update initial address value)

end UpdateProgram


inductive LogicalAddress (maxNodes degree : ℕ) where
  | state
  | nodeLabel (node : Fin maxNodes)
  | nodeEdge (node : Fin maxNodes) (port : Fin degree)
  deriving DecidableEq, Fintype

structure Packing
    (wordBits maxNodes stateCount workLabelCount degree : ℕ) where
  addressCapacity :
    Fintype.card (LogicalAddress maxNodes degree) ≤ 2 ^ wordBits
  stateCapacity : stateCount ≤ 2 ^ wordBits
  labelCapacity : Fintype.card (Option (Fin workLabelCount)) ≤ 2 ^ wordBits
  offsetCapacity : Fintype.card (Option (Fin maxNodes)) ≤ 2 ^ wordBits

noncomputable def packFinite {wordBits : ℕ} {Value : Type}
    [Fintype Value] (capacity : Fintype.card Value ≤ 2 ^ wordBits)
    (value : Value) : BitVec wordBits :=
  BitVec.ofFin (Fin.castLE capacity (Fintype.equivFin Value value))

noncomputable def unpackFinite {wordBits : ℕ} {Value : Type}
    [Fintype Value] (word : BitVec wordBits) : Option Value :=
  if inRange : word.toNat < Fintype.card Value then
    some ((Fintype.equivFin Value).symm ⟨word.toNat, inRange⟩)
  else
    none

@[simp] theorem unpackFinite_packFinite {wordBits : ℕ} {Value : Type}
    [Fintype Value] (capacity : Fintype.card Value ≤ 2 ^ wordBits)
    (value : Value) :
    unpackFinite (packFinite capacity value) = some value := by
  simp [unpackFinite, packFinite]

theorem packFinite_injective {wordBits : ℕ} {Value : Type}
    [Fintype Value] (capacity : Fintype.card Value ≤ 2 ^ wordBits) :
    Function.Injective (packFinite capacity : Value → BitVec wordBits) := by
  intro left right equality
  have hfin := congrArg BitVec.toFin equality
  have hval : (Fintype.equivFin Value left).val =
      (Fintype.equivFin Value right).val := by
    simpa [packFinite] using congrArg Fin.val hfin
  exact (Fintype.equivFin Value).injective (Fin.ext hval)

namespace Packing

variable {wordBits maxNodes stateCount workLabelCount degree : ℕ}

noncomputable def address
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (logical : LogicalAddress maxNodes degree) : CellProbe.Address wordBits :=
  packFinite packing.addressCapacity logical

theorem address_injective
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree) :
    Function.Injective packing.address :=
  packFinite_injective packing.addressCapacity

noncomputable def stateWord
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (state : Fin stateCount) : CellProbe.Word wordBits :=
  packFinite (by simpa using packing.stateCapacity) state

noncomputable def labelWord
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (label : Option (Fin workLabelCount)) : CellProbe.Word wordBits :=
  packFinite packing.labelCapacity label

noncomputable def offsetWord
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (offset : Option (Fin maxNodes)) : CellProbe.Word wordBits :=
  packFinite packing.offsetCapacity offset

def boundedOffset (maxNodes : ℕ) : Option ℕ → Option (Fin maxNodes)
  | none => none
  | some offset => if h : offset < maxNodes then some ⟨offset, h⟩ else none

noncomputable def logicalValue
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (configuration : Configuration stateCount workLabelCount degree) :
    LogicalAddress maxNodes degree → CellProbe.Word wordBits
  | .state => packing.stateWord configuration.1
  | .nodeLabel node =>
      packing.labelWord ((configuration.2.nodes[node.val]?).bind Node.label)
  | .nodeEdge node port =>
      packing.offsetWord
        (boundedOffset maxNodes
          ((configuration.2.nodes[node.val]?).bind (fun n => n.edgeOffset port)))

noncomputable def encodeMemory
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (configuration : Configuration stateCount workLabelCount degree) :
    FiniteMemory wordBits := fun physical =>
  if existsLogical : ∃ logical, packing.address logical = physical then
    packing.logicalValue configuration (Classical.choose existsLogical)
  else
    0

theorem encodeMemory_read
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (configuration : Configuration stateCount workLabelCount degree)
    (logical : LogicalAddress maxNodes degree) :
    packing.encodeMemory configuration (packing.address logical) =
      packing.logicalValue configuration logical := by
  classical
  unfold encodeMemory
  split
  next existsLogical =>
    have chosen_eq : Classical.choose existsLogical = logical :=
      packing.address_injective (Classical.choose_spec existsLogical)
    rw [chosen_eq]
  next noLogical =>
    exact (noLogical ⟨logical, rfl⟩).elim

def nodeRecordLogical (node : Fin maxNodes) :
    List (LogicalAddress maxNodes degree) :=
  .nodeLabel node :: List.ofFn (fun port => .nodeEdge node port)

@[simp] theorem nodeRecordLogical_length (node : Fin maxNodes) :
    (nodeRecordLogical (degree := degree) node).length = degree + 1 := by
  simp [nodeRecordLogical]

noncomputable def nodeRecordAddresses
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (node : Fin maxNodes) : List (CellProbe.Address wordBits) :=
  (nodeRecordLogical (degree := degree) node).map packing.address

@[simp] theorem nodeRecordAddresses_length
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (node : Fin maxNodes) :
    (packing.nodeRecordAddresses node).length = degree + 1 := by
  simp [nodeRecordAddresses]

noncomputable def readNodeRecord
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (node : Fin maxNodes) :
    ReadProgram wordBits (List (CellProbe.Word wordBits))
      (packing.nodeRecordAddresses node).length :=
  ReadProgram.readCells (packing.nodeRecordAddresses node)

theorem readNodeRecord_trace_length
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (node : Fin maxNodes) (memory : FiniteMemory wordBits) :
    ((packing.readNodeRecord node).execute memory).trace.length = degree + 1 :=
  (ReadProgram.execute_trace_length memory (packing.readNodeRecord node)).trans
    (packing.nodeRecordAddresses_length node)

theorem readNodeRecord_encode_result
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (configuration : Configuration stateCount workLabelCount degree)
    (node : Fin maxNodes) :
    ((packing.readNodeRecord node).execute
        (packing.encodeMemory configuration)).result =
      (nodeRecordLogical (degree := degree) node).map
        (packing.logicalValue configuration) := by
  rw [readNodeRecord, ReadProgram.readCells_result]
  simp [nodeRecordAddresses, Function.comp_def, encodeMemory_read]

def OffsetsFit
    (configuration : Configuration stateCount workLabelCount degree)
    (maxNodes : ℕ) : Prop :=
  ∀ node ∈ configuration.2.nodes, ∀ port offset,
    node.edgeOffset port = some offset → offset < maxNodes

end Packing


def pathOccurrences (degree : ℕ) : ℕ → ℕ
  | 0 => 1
  | radius + 1 => 1 + degree * pathOccurrences degree radius

def perSymbolBudget (degree radius : ℕ) : ℕ :=
  (degree + 1) * pathOccurrences degree radius + (degree + 3)

def indexWidth (n : ℕ) : ℕ := Nat.clog 2 (n ^ 2 + 1)

def hardQueryLength (n : ℕ) : ℕ := 1 + indexWidth n

theorem indexWidth_le_two_clog (n : ℕ) :
    indexWidth n ≤ 2 * Nat.clog 2 (n + 1) := by
  apply Nat.clog_le_of_le_pow
  let k := Nat.clog 2 (n + 1)
  have hk : n + 1 ≤ 2 ^ k := Nat.le_pow_clog Nat.one_lt_two _
  calc
    n ^ 2 + 1 ≤ (n + 1) ^ 2 := by nlinarith
    _ ≤ (2 ^ k) ^ 2 := by nlinarith
    _ = 2 ^ (2 * k) := by
      rw [← Nat.pow_mul]
      congr 1
      omega

theorem hardQueryLength_le (n : ℕ) :
    hardQueryLength n ≤ 1 + 2 * Nat.clog 2 (n + 1) := by
  exact Nat.add_le_add_left (indexWidth_le_two_clog n) 1

theorem hardQueryNumericalBound (degree radius n : ℕ) :
    hardQueryLength n * perSymbolBudget degree radius ≤
      (1 + 2 * Nat.clog 2 (n + 1)) * perSymbolBudget degree radius := by
  exact Nat.mul_le_mul_right _ (hardQueryLength_le n)

end PegSeparation.Reduction.SCAToCellProbe
