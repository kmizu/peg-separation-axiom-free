import PegSeparation.CFLNotPEG.Reduction.SCAPackingBounds
import PegSeparation.CFLNotPEG.Reduction.SCAQueryCompiler


namespace PegSeparation.Reduction.SCAFamilyCompiler

open PegSeparation.Scaffolding
open PegSeparation.Reduction.SCAToCellProbe
open PegSeparation.Reduction.SCACompiler
open PegSeparation.Reduction.SCACompiler.StableGraph
open PegSeparation.Reduction.SCACompiler.GraphPacking
open PegSeparation.Reduction.SCACompiler.ViewCompiler
open PegSeparation.Reduction.SCACompiler.StepCompiler
open PegSeparation.Reduction.SCABisimulation
open PegSeparation.Reduction.SCAQueryCompiler
open PegSeparation.Reduction.SCAPackingBounds
open PegSeparation.Reduction.HardMultiphase
open PegSeparation.Reduction.MultiphaseModel
open PegSeparation.Witness.HardSlice

def phaseCount (n : ℕ) : ℕ :=
  rowCount n * (keyWidth n + n + 3) + 2

def updateReads (degree radius : ℕ) : ℕ :=
  viewBudget degree radius + 1

def updateWrites (degree : ℕ) : ℕ :=
  finBudget 1 degree + 2

def queryScale (degree radius : ℕ) : ℕ :=
  2 * perSymbolBudget degree radius

theorem phaseCount_pos (n : ℕ) : 0 < phaseCount n := by
  unfold phaseCount
  omega

theorem phase_space {n : ℕ} (S : Matrix n) :
    (hardPhaseI S).length + 1 ≤ maxNodes n := by
  rw [hardPhaseI_length]
  have fit := hard_nodes_fit n
  omega

theorem full_space {n : ℕ} (S : Matrix n)
    (q : Fin (rowCount n)) :
    (hardPhaseI S).length + 1 + n + (hardQuerySuffix q).length ≤
      maxNodes n := by
  rw [hardPhaseI_length, hardQuerySuffix_length]
  have fit := hard_nodes_fit n
  omega

theorem update_room {n : ℕ} (coordinate : Fin n) :
    phaseCount n + coordinate.val < maxNodes n := by
  have fit := hard_nodes_fit n
  unfold phaseCount
  omega

theorem query_space {n : ℕ} (q : Fin (rowCount n)) :
    phaseCount n + n + (hardQuerySuffix q).length ≤ maxNodes n := by
  have fit := hard_nodes_fit n
  rw [hardQuerySuffix_length]
  unfold phaseCount
  exact fit

noncomputable def phaseRun
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (S : Matrix n) :
    Σ graph : StableGraph stateCount workLabelCount (maxNodes n) degree,
      ConfigurationCorresponds graph (automaton.run (hardPhaseI S)) :=
  initialRunCorrespondence automaton (hardPhaseI S) (phase_space S)

noncomputable def phaseGraph
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (S : Matrix n) :
    StableGraph stateCount workLabelCount (maxNodes n) degree :=
  (phaseRun automaton S).1

noncomputable def phaseRelation
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (S : Matrix n) :
    ConfigurationCorresponds (phaseGraph automaton S)
      (automaton.run (hardPhaseI S)) :=
  (phaseRun automaton S).2

theorem phaseGraph_count
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (S : Matrix n) :
    (phaseGraph automaton S).count = phaseCount n := by
  unfold phaseGraph phaseRun phaseCount
  rw [initialRunCorrespondence_count]
  rw [hardPhaseI_length]

noncomputable def preprocess
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (S : Matrix n) :
    FiniteMemory (wordBits stateCount workLabelCount degree n) :=
  GraphPacking.encodeGraph
    (packing stateCount workLabelCount degree n)
    (phaseGraph automaton S)

theorem preprocess_represents
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (S : Matrix n) :
    GraphPacking.Represents
      (packing stateCount workLabelCount degree n)
      (preprocess automaton S) (phaseGraph automaton S) :=
  GraphPacking.encodeGraph_represents _ _

def discardUpdateResult {wordBits reads writes : ℕ} {Result : Type}
    (program : UpdateProgram wordBits Result reads writes) :
    UpdateProgram wordBits Unit reads writes :=
  match program with
  | .done _ => .done ()
  | .read address next =>
      .read address fun value => discardUpdateResult (next value)
  | .write address value next =>
      .write address value (discardUpdateResult next)

theorem discardUpdateResult_memory {wordBits reads writes : ℕ}
    {Result : Type}
    (program : UpdateProgram wordBits Result reads writes)
    (memory : FiniteMemory wordBits) :
    ((discardUpdateResult program).execute memory).memory =
      (program.execute memory).memory := by
  induction program generalizing memory with
  | done => rfl
  | read address next ih =>
      exact ih (memory address) memory
  | write address value next ih =>
      exact ih (Function.update memory address value)

noncomputable def compileUpdate
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (coordinate : Fin n) (bit : Bool) :
    UpdateProgram (wordBits stateCount workLabelCount degree n) Unit
      (updateReads degree radius) (updateWrites degree) :=
  discardUpdateResult <|
    compileStep automaton (packing stateCount workLabelCount degree n)
      ((packing stateCount workLabelCount degree n).address .state)
      (phaseCount n + coordinate.val)
      (by have := phaseCount_pos n; omega)
      (update_room coordinate)
      (PegSeparation.Witness.LanguageCFG.bitTerminal bit)

theorem compileUpdate_memory
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (coordinate : Fin n) (bit : Bool)
    (memory : FiniteMemory (wordBits stateCount workLabelCount degree n)) :
    ((compileUpdate automaton coordinate bit).execute memory).memory =
      ((compileStep automaton (packing stateCount workLabelCount degree n)
        ((packing stateCount workLabelCount degree n).address .state)
        (phaseCount n + coordinate.val)
        (by have := phaseCount_pos n; omega)
        (update_room coordinate)
        (PegSeparation.Witness.LanguageCFG.bitTerminal bit)).execute
          memory).memory := by
  rw [compileUpdate, discardUpdateResult_memory]
  congr

def updatePrefix {n : ℕ} (X : Vector n) (length : ℕ)
    (within : length ≤ n) : List (Fin n × Bool) :=
  List.ofFn fun coordinate : Fin length =>
    let lifted : Fin n := Fin.castLE within coordinate
    (lifted, X lifted)

def bitPrefix {n : ℕ} (X : Vector n) (length : ℕ)
    (within : length ≤ n) : List Bool :=
  (updatePrefix X length within).map Prod.snd

theorem updatePrefix_succ {n : ℕ} (X : Vector n) (length : ℕ)
    (within : length + 1 ≤ n) :
    updatePrefix X (length + 1) within =
      updatePrefix X length (by omega) ++
        [(⟨length, by omega⟩, X ⟨length, by omega⟩)] := by
  unfold updatePrefix
  rw [List.ofFn_succ', List.concat_eq_append]
  congr 1

theorem bitPrefix_succ {n : ℕ} (X : Vector n) (length : ℕ)
    (within : length + 1 ≤ n) :
    bitPrefix X (length + 1) within =
      bitPrefix X length (by omega) ++ [X ⟨length, by omega⟩] := by
  unfold bitPrefix
  rw [updatePrefix_succ]
  simp

theorem updatePrefix_full {n : ℕ} (X : Vector n) :
    updatePrefix X n (Nat.le_refl n) =
      List.ofFn fun coordinate => (coordinate, X coordinate) := by
  unfold updatePrefix
  apply List.ofFn_congr rfl

theorem bitPrefix_full {n : ℕ} (X : Vector n) :
    bitPrefix X n (Nat.le_refl n) = List.ofFn X := by
  unfold bitPrefix
  rw [updatePrefix_full]
  simp [List.map_ofFn, Function.comp_def]

noncomputable def prefixMemory
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (S : Matrix n) (X : Vector n) (length : ℕ) (within : length ≤ n) :
    FiniteMemory (wordBits stateCount workLabelCount degree n) :=
  runUpdateList (compileUpdate automaton) (preprocess automaton S)
    (updatePrefix X length within)

def prefixConfiguration
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (S : Matrix n) (X : Vector n) (length : ℕ) (within : length ≤ n) :
    Fin stateCount × Scaffold (Fin workLabelCount) degree :=
  QueryOverlay.runFrom automaton (automaton.run (hardPhaseI S))
    (bitWord (bitPrefix X length within))

theorem prefixMemory_succ
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (S : Matrix n) (X : Vector n) (length : ℕ)
    (within : length + 1 ≤ n) :
    prefixMemory automaton S X (length + 1) within =
      ((compileUpdate automaton ⟨length, by omega⟩
        (X ⟨length, by omega⟩)).execute
          (prefixMemory automaton S X length (by omega))).memory := by
  unfold prefixMemory
  rw [updatePrefix_succ, runUpdateList_append]
  rfl

theorem prefixConfiguration_succ
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (S : Matrix n) (X : Vector n) (length : ℕ)
    (within : length + 1 ≤ n) :
    prefixConfiguration automaton S X (length + 1) within =
      automaton.step (prefixConfiguration automaton S X length (by omega))
        (PegSeparation.Witness.LanguageCFG.bitTerminal
          (X ⟨length, by omega⟩)) := by
  unfold prefixConfiguration
  rw [bitPrefix_succ]
  simp only [bitWord,
    PegSeparation.Witness.LanguageCFG.bitWord_append,
    QueryOverlay.runFrom_append]
  rfl

structure CompiledState
    {wordBits maxNodes stateCount workLabelCount degree : ℕ}
    (packing : Packing wordBits maxNodes stateCount workLabelCount degree)
    (memory : FiniteMemory wordBits)
    (configuration : Fin stateCount × Scaffold (Fin workLabelCount) degree)
    (count : ℕ) : Type where
  graph : StableGraph stateCount workLabelCount maxNodes degree
  count_eq : graph.count = count
  represents : GraphPacking.Represents packing memory graph
  relation : ConfigurationCorresponds graph configuration

noncomputable def phaseState
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (S : Matrix n) :
    CompiledState (packing stateCount workLabelCount degree n)
      (preprocess automaton S) (automaton.run (hardPhaseI S))
      (phaseCount n) :=
  { graph := phaseGraph automaton S
    count_eq := phaseGraph_count automaton S
    represents := preprocess_represents automaton S
    relation := phaseRelation automaton S }

noncomputable def advanceCoordinate
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (coordinate : Fin n) (bit : Bool)
    (memory : FiniteMemory (wordBits stateCount workLabelCount degree n))
    (configuration : Fin stateCount × Scaffold (Fin workLabelCount) degree)
    (current : CompiledState
      (packing stateCount workLabelCount degree n) memory configuration
      (phaseCount n + coordinate.val)) :
    CompiledState (packing stateCount workLabelCount degree n)
      ((compileUpdate automaton coordinate bit).execute memory).memory
      (automaton.step configuration
        (PegSeparation.Witness.LanguageCFG.bitTerminal bit))
      (phaseCount n + coordinate.val + 1) := by
  let symbol := PegSeparation.Witness.LanguageCFG.bitTerminal bit
  have graphRoom : current.graph.count < maxNodes n := by
    rw [current.count_eq]
    exact update_room coordinate
  let nextGraph := stableStep automaton current.graph graphRoom symbol
  have persistentMemory :
      ((compileUpdate automaton coordinate bit).execute memory).memory =
        ((compileStep automaton
          (packing stateCount workLabelCount degree n)
          ((packing stateCount workLabelCount degree n).address .state)
          current.graph.count current.graph.count_pos graphRoom symbol).execute
            memory).memory := by
    rw [compileUpdate_memory]
    simp only [current.count_eq]
    rfl
  refine
    { graph := nextGraph
      count_eq := ?_
      represents := ?_
      relation := ?_ }
  · dsimp [nextGraph]
    rw [current.count_eq]
  · rw [persistentMemory]
    exact compileStep_preserves_representation automaton
      (packing stateCount workLabelCount degree n)
      ((packing stateCount workLabelCount degree n).address .state)
      memory current.graph graphRoom current.represents symbol
  · exact current.relation.step automaton graphRoom symbol

noncomputable def prefixState
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (S : Matrix n) (X : Vector n) (length : ℕ) (within : length ≤ n) :
    CompiledState (packing stateCount workLabelCount degree n)
      (prefixMemory automaton S X length within)
      (prefixConfiguration automaton S X length within)
      (phaseCount n + length) := by
  induction length with
  | zero =>
      simpa [prefixMemory, prefixConfiguration, updatePrefix, bitPrefix,
        bitWord, QueryOverlay.runFrom, runUpdateList] using
          phaseState automaton S
  | succ length ih =>
      have previous := ih (by omega : length ≤ n)
      let coordinate : Fin n := ⟨length, by omega⟩
      have advanced := advanceCoordinate automaton coordinate (X coordinate)
        (prefixMemory automaton S X length (by omega))
        (prefixConfiguration automaton S X length (by omega)) previous
      rw [prefixMemory_succ, prefixConfiguration_succ]
      simpa [coordinate, Nat.add_assoc] using advanced

theorem prefixMemory_full
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (S : Matrix n) (X : Vector n) :
    prefixMemory automaton S X n (Nat.le_refl n) =
      runAllUpdates (compileUpdate automaton) (preprocess automaton S) X := by
  unfold prefixMemory runAllUpdates
  rw [updatePrefix_full]

theorem prefixConfiguration_full
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (S : Matrix n) (X : Vector n) :
    prefixConfiguration automaton S X n (Nat.le_refl n) =
      QueryOverlay.runFrom automaton (automaton.run (hardPhaseI S))
        (hardUpdates X) := by
  unfold prefixConfiguration hardUpdates
  rw [bitPrefix_full]

noncomputable def finalUpdateState
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (S : Matrix n) (X : Vector n) :
    CompiledState (packing stateCount workLabelCount degree n)
      (runAllUpdates (compileUpdate automaton) (preprocess automaton S) X)
      (QueryOverlay.runFrom automaton (automaton.run (hardPhaseI S))
        (hardUpdates X))
      (phaseCount n + n) := by
  rw [← prefixMemory_full automaton S X,
    ← prefixConfiguration_full automaton S X]
  exact prefixState automaton S X n (Nat.le_refl n)

def queryReads (degree radius n : ℕ) : ℕ :=
  scaledLogBudget (queryScale degree radius) n

noncomputable def compileFamilyQuery
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (q : Fin (rowCount n)) :
    ReadProgram (wordBits stateCount workLabelCount degree n) Bool
      (queryReads degree radius n) :=
  let pack := packing stateCount workLabelCount degree n
  let dummy := pack.address .state
  let actual := compileQuery automaton pack dummy (phaseCount n + n)
    (by have := phaseCount_pos n; omega)
    (by have := query_space q; omega)
    (hardQuerySuffix q) (query_space q)
  ReadProgram.padTo dummy (by
    simpa [queryReads, queryScale, MultiphaseModel.scaledLogBudget,
      MultiphaseModel.logScale] using
      (hardQuery_budget_le_scaled
        (degree := degree) (radius := radius) q)) actual

theorem compileFamilyQuery_correct
    {stateCount workLabelCount degree radius n : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (decidesC : ∀ word, automaton.Accepts word ↔
      word ∈ PegSeparation.Witness.LanguageCFG.C)
    (S : Matrix n) (X : Vector n) (q : Fin (rowCount n)) :
    ((compileFamilyQuery automaton q).execute
      (runAllUpdates (compileUpdate automaton) (preprocess automaton S) X)).result =
        innerProductAnswer S X q := by
  let current := finalUpdateState automaton S X
  have graphSpace : current.graph.count + (hardQuerySuffix q).length ≤
      maxNodes n := by
    rw [current.count_eq]
    exact query_space q
  have compiled := compileHardQuery_correct automaton decidesC
    (packing stateCount workLabelCount degree n)
    ((packing stateCount workLabelCount degree n).address .state)
    (runAllUpdates (compileUpdate automaton) (preprocess automaton S) X)
    S X q current.graph current.represents current.relation graphSpace
  unfold compileFamilyQuery
  rw [ReadProgram.padTo_execute_result]
  simpa [current.count_eq, innerProductAnswer] using compiled

noncomputable def compileAtDimension
    {stateCount workLabelCount degree radius : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (decidesC : ∀ word, automaton.Accepts word ↔
      word ∈ PegSeparation.Witness.LanguageCFG.C)
    (n : ℕ) :
    ExactMultiphaseIP n
      (scaledLogBudget (wordScale stateCount workLabelCount degree) n)
      (updateReads degree radius) (updateWrites degree)
      (scaledLogBudget (queryScale degree radius) n) :=
  { preprocess := preprocess automaton
    update := compileUpdate automaton
    query := compileFamilyQuery automaton
    correct := compileFamilyQuery_correct automaton decidesC }

theorem fastMultiphaseIPFamily_of_SCA
    {stateCount workLabelCount degree radius : ℕ}
    (automaton : Automaton Alphabet stateCount workLabelCount degree radius)
    (decidesC : ∀ word, automaton.Accepts word ↔
      word ∈ PegSeparation.Witness.LanguageCFG.C) :
    HasFastMultiphaseIPFamily := by
  refine ⟨wordScale stateCount workLabelCount degree,
    queryScale degree radius, updateReads degree radius,
    updateWrites degree, ?_, ?_, ?_⟩
  · unfold wordScale
    omega
  · unfold queryScale perSymbolBudget
    omega
  · intro n hn
    exact ⟨compileAtDimension automaton decidesC n⟩

end PegSeparation.Reduction.SCAFamilyCompiler
