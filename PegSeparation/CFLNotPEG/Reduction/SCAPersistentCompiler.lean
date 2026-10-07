import PegSeparation.CFLNotPEG.Reduction.SCAQueryCompiler
import PegSeparation.CFLNotPEG.Reduction.ThreeStageModel


namespace PegSeparation.Reduction.SCAPersistentCompiler

open PegSeparation.Scaffolding
open PegSeparation.CellProbe
open PegSeparation.Reduction.SCAToCellProbe
open PegSeparation.Reduction.SCACompiler
open PegSeparation.Reduction.SCACompiler.StableGraph
open PegSeparation.Reduction.SCACompiler.GraphPacking
open PegSeparation.Reduction.SCACompiler.ViewCompiler
open PegSeparation.Reduction.SCACompiler.StepCompiler
open PegSeparation.Reduction.SCABisimulation
open PegSeparation.Reduction.SCAQueryCompiler

structure CountedPacking
    (wordBits maxNodes stateCount workLabelCount degree : ℕ) where
  core : Packing wordBits maxNodes stateCount workLabelCount degree
  countAddress : CellProbe.Address wordBits
  countFresh : ∀ logical, core.address logical ≠ countAddress
  countCapacity : maxNodes + 1 ≤ 2 ^ wordBits

namespace CountedPacking

variable {wordBits maxNodes stateCount workLabelCount degree : ℕ}

noncomputable def countWord
    (packing : CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (count : Fin (maxNodes + 1)) : CellProbe.Word wordBits :=
  packFinite (by simpa using packing.countCapacity) count

noncomputable def decodeCount
    (word : CellProbe.Word wordBits) : ℕ :=
  ((unpackFinite word : Option (Fin (maxNodes + 1))).getD 0).val

@[simp] theorem decodeCount_countWord
    (packing : CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (count : Fin (maxNodes + 1)) :
    decodeCount (maxNodes := maxNodes) (packing.countWord count) =
      count.val := by
  simp [decodeCount, countWord]

def Represents
    (packing : CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (memory : FiniteMemory wordBits)
    (graph : StableGraph stateCount workLabelCount maxNodes degree) : Prop :=
  GraphPacking.Represents packing.core memory graph ∧
    memory packing.countAddress =
      packing.countWord ⟨graph.count, Nat.lt_succ_of_le graph.count_le⟩

noncomputable def encode
    (packing : CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (graph : StableGraph stateCount workLabelCount maxNodes degree) :
    FiniteMemory wordBits :=
  Function.update (GraphPacking.encodeGraph packing.core graph)
    packing.countAddress
    (packing.countWord ⟨graph.count, Nat.lt_succ_of_le graph.count_le⟩)

theorem encode_represents
    (packing : CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (graph : StableGraph stateCount workLabelCount maxNodes degree) :
    packing.Represents (packing.encode graph) graph := by
  constructor
  · intro logical
    rw [encode, Function.update_of_ne]
    · exact GraphPacking.encodeGraph_read packing.core graph logical
    · exact packing.countFresh logical
  · simp [encode]

theorem core_of_represents
    (packing : CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (memory : FiniteMemory wordBits)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (represents : packing.Represents memory graph) :
    GraphPacking.Represents packing.core memory graph :=
  represents.1

theorem decoded_count
    (packing : CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (memory : FiniteMemory wordBits)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (represents : packing.Represents memory graph) :
    decodeCount (maxNodes := maxNodes) (memory packing.countAddress) =
      graph.count := by
  rw [represents.2, decodeCount_countWord]

end CountedPacking


variable {Terminal : Type}
variable {wordBits maxNodes stateCount workLabelCount degree radius : ℕ}

def blockBudget (each : ℕ) : List Terminal → ℕ
  | [] => 0
  | _ :: rest => blockBudget each rest + each

theorem blockBudget_eq (each : ℕ) (symbols : List Terminal) :
    blockBudget each symbols = symbols.length * each := by
  induction symbols with
  | nil => simp [blockBudget]
  | cons symbol rest ih =>
      simp [blockBudget, ih, Nat.succ_mul]

def stepReads (degree radius : ℕ) : ℕ :=
  viewBudget degree radius + 1

def stepWrites (degree : ℕ) : ℕ :=
  finBudget 1 degree + 2

noncomputable def compileCoreBlock
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits) :
    (count : ℕ) → 0 < count → (symbols : List Terminal) →
      count + symbols.length ≤ maxNodes →
      UpdateProgram wordBits Unit
        (blockBudget (stepReads degree radius) symbols)
        (blockBudget (stepWrites degree) symbols)
  | _, _, [], _ => .done ()
  | count, countPos, symbol :: rest, space =>
      let room : count < maxNodes := by
        simp only [List.length_cons] at space
        omega
      let nextSpace : count + 1 + rest.length ≤ maxNodes := by
        simp only [List.length_cons] at space
        omega
      (compileStep automaton packing dummyAddress count countPos room
        symbol).bind fun _ =>
          compileCoreBlock automaton packing dummyAddress (count + 1)
            (by omega) rest nextSpace

theorem compileCoreBlock_represents
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (dummyAddress : CellProbe.Address wordBits)
    (memory : FiniteMemory wordBits)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (configuration : Fin stateCount × Scaffold (Fin workLabelCount) degree)
    (relation : ConfigurationCorresponds graph configuration)
    (represents : GraphPacking.Represents packing memory graph)
    (symbols : List Terminal)
    (space : graph.count + symbols.length ≤ maxNodes) :
    GraphPacking.Represents packing
      ((compileCoreBlock automaton packing dummyAddress graph.count
        graph.count_pos symbols space).execute memory).memory
      (runCorrespondence automaton relation symbols space).1 := by
  induction symbols generalizing memory graph configuration with
  | nil => exact represents
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
      let first := compileStep automaton packing dummyAddress graph.count
        graph.count_pos room symbol
      have firstRepresents :
          GraphPacking.Represents packing
            (first.execute memory).memory
            (stableStep automaton graph room symbol) := by
        exact compileStep_preserves_representation automaton packing
          dummyAddress memory graph room represents symbol
      change
        GraphPacking.Represents packing
          (((first.bind fun _ =>
            compileCoreBlock automaton packing dummyAddress
              (graph.count + 1) (by omega) rest (by
                simp only [List.length_cons] at space
                omega)).execute memory).memory)
          (runCorrespondence automaton relation (symbol :: rest) space).1
      rw [UpdateProgram.bind_execute_memory]
      change
        GraphPacking.Represents packing
          ((compileCoreBlock automaton packing dummyAddress
            (graph.count + 1) (by omega) rest (by
              simpa only [stableStep_count] using nextSpace)).execute
                (first.execute memory).memory).memory
          (runCorrespondence automaton nextRelation rest nextSpace).1
      simpa only [stableStep_count] using
        ih (memory := first.execute memory |>.memory)
          (graph := stableStep automaton graph room symbol)
          (configuration := automaton.step configuration symbol)
          (relation := nextRelation)
          (represents := firstRepresents) (space := nextSpace)

def dummyUpdate (address : CellProbe.Address wordBits) :
    (reads writes : ℕ) → UpdateProgram wordBits Unit reads writes
  | 0, 0 => .done ()
  | reads + 1, writes =>
      .read address fun _ => dummyUpdate address reads writes
  | 0, writes + 1 =>
      .write address 0 (dummyUpdate address 0 writes)

def updateReadBudget (degree radius : ℕ) (symbols : List Terminal) : ℕ :=
  blockBudget (stepReads degree radius) symbols + 1

def updateWriteBudget (degree : ℕ) (symbols : List Terminal) : ℕ :=
  blockBudget (stepWrites degree) symbols + 1

noncomputable def compileUpdateBlock
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing :
      CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (symbols : List Terminal) :
    UpdateProgram wordBits Unit
      (updateReadBudget degree radius symbols)
      (updateWriteBudget degree symbols) :=
  .read packing.countAddress fun countWord =>
    let count := CountedPacking.decodeCount
      (maxNodes := maxNodes) countWord
    if countPos : 0 < count then
      if space : count + symbols.length ≤ maxNodes then
        reindexUpdate (by simp) (by
          simp only [updateWriteBudget]
          omega) <|
          (compileCoreBlock automaton packing.core packing.countAddress count
            countPos symbols space).bind fun _ =>
              .write packing.countAddress
                (packing.countWord
                  ⟨count + symbols.length, Nat.lt_succ_of_le space⟩)
                (.done ())
      else
        dummyUpdate packing.countAddress
          (blockBudget (stepReads degree radius) symbols)
          (updateWriteBudget degree symbols)
    else
      dummyUpdate packing.countAddress
        (blockBudget (stepReads degree radius) symbols)
        (updateWriteBudget degree symbols)

theorem compileUpdateBlock_represents
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing :
      CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (symbols : List Terminal)
    (memory : FiniteMemory wordBits)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (configuration : Fin stateCount × Scaffold (Fin workLabelCount) degree)
    (relation : ConfigurationCorresponds graph configuration)
    (represents : packing.Represents memory graph)
    (space : graph.count + symbols.length ≤ maxNodes) :
    packing.Represents
      ((compileUpdateBlock automaton packing symbols).execute memory).memory
      (runCorrespondence automaton relation symbols space).1 := by
  have decoded :
      CountedPacking.decodeCount (maxNodes := maxNodes)
          (memory packing.countAddress) = graph.count :=
    packing.decoded_count memory graph represents
  have coreRepresents :
      GraphPacking.Represents packing.core
        ((compileCoreBlock automaton packing.core packing.countAddress
          graph.count graph.count_pos symbols space).execute memory).memory
        (runCorrespondence automaton relation symbols space).1 :=
    compileCoreBlock_represents automaton packing.core packing.countAddress
      memory graph configuration relation represents.1 symbols space
  simp only [compileUpdateBlock, UpdateProgram.execute, decoded,
    dif_pos graph.count_pos, dif_pos space]
  rw [reindexUpdate_execute, UpdateProgram.bind_execute_memory]
  simp only [UpdateProgram.execute]
  let coreMemory :=
    ((compileCoreBlock automaton packing.core packing.countAddress
      graph.count graph.count_pos symbols space).execute memory).memory
  constructor
  · intro logical
    rw [Function.update_of_ne]
    · exact coreRepresents logical
    · exact packing.countFresh logical
  · rw [Function.update_self]
    apply congrArg packing.countWord
    exact Fin.ext
      (runCorrespondence_count automaton relation symbols space).symm

theorem compileUpdateBlock_read_count
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing :
      CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (symbols : List Terminal) (memory : FiniteMemory wordBits) :
    ((compileUpdateBlock automaton packing symbols).execute memory).readTrace.length =
      1 + symbols.length * stepReads degree radius := by
  rw [UpdateProgram.execute_readTrace_length, updateReadBudget,
    blockBudget_eq]
  omega

theorem compileUpdateBlock_write_count
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing :
      CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (symbols : List Terminal) (memory : FiniteMemory wordBits) :
    ((compileUpdateBlock automaton packing symbols).execute memory).writes.length =
      1 + symbols.length * stepWrites degree := by
  rw [UpdateProgram.execute_writes_length, updateWriteBudget,
    blockBudget_eq]
  omega


def countedQueryBudget (degree radius : ℕ)
    (symbols : List Terminal) : ℕ :=
  queryBudget degree radius symbols + 1

noncomputable def compileCountedQuery
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing :
      CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (symbols : List Terminal) :
    ReadProgram wordBits Bool (countedQueryBudget degree radius symbols) :=
  .probe packing.countAddress fun countWord =>
    let count := CountedPacking.decodeCount
      (maxNodes := maxNodes) countWord
    if countPos : 0 < count then
      if space : count + symbols.length ≤ maxNodes then
        compileQuery automaton packing.core packing.countAddress count
          countPos (Nat.le_trans (Nat.le_add_right count symbols.length)
            space) symbols space
      else
        ReadProgram.pad packing.countAddress false
          (queryBudget degree radius symbols)
    else
      ReadProgram.pad packing.countAddress false
        (queryBudget degree radius symbols)

theorem compileCountedQuery_correct
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing :
      CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (symbols : List Terminal)
    (memory : FiniteMemory wordBits)
    (graph : StableGraph stateCount workLabelCount maxNodes degree)
    (configuration : Fin stateCount × Scaffold (Fin workLabelCount) degree)
    (relation : ConfigurationCorresponds graph configuration)
    (represents : packing.Represents memory graph)
    (space : graph.count + symbols.length ≤ maxNodes) :
    ((compileCountedQuery automaton packing symbols).execute memory).result =
      decide ((QueryOverlay.runFrom automaton configuration symbols).1 ∈
        automaton.accepting) := by
  have decoded :
      CountedPacking.decodeCount (maxNodes := maxNodes)
          (memory packing.countAddress) = graph.count :=
    packing.decoded_count memory graph represents
  simp only [compileCountedQuery, ReadProgram.execute, decoded,
    dif_pos graph.count_pos, dif_pos space]
  exact compileQuery_correct automaton packing.core packing.countAddress
    memory graph represents.1 configuration relation symbols space

theorem compileCountedQuery_probe_count
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing :
      CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (symbols : List Terminal) (memory : FiniteMemory wordBits) :
    ((compileCountedQuery automaton packing symbols).execute memory).trace.length =
      2 + symbols.length * viewBudget degree radius := by
  rw [ReadProgram.execute_trace_length, countedQueryBudget, queryBudget_eq]
  omega

end PegSeparation.Reduction.SCAPersistentCompiler
