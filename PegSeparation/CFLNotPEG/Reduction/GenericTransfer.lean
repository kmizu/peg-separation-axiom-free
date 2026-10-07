import PegSeparation.CFLNotPEG.Reduction.GenericPackingBounds


namespace PegSeparation.Reduction.GenericTransfer

open PegSeparation.Scaffolding
open PegSeparation.Reduction.SCAToCellProbe
open PegSeparation.Reduction.SCACompiler
open PegSeparation.Reduction.SCACompiler.StableGraph
open PegSeparation.Reduction.SCACompiler.GraphPacking
open PegSeparation.Reduction.SCACompiler.ViewCompiler
open PegSeparation.Reduction.SCABisimulation
open PegSeparation.Reduction.SCAQueryCompiler
open PegSeparation.Reduction.SCAPersistentCompiler
open PegSeparation.Reduction.ThreeStageModel

variable {Terminal : Type}
variable {stateCount workLabelCount degree radius wordBits maxNodes : ℕ}
variable {problem : Problem}

def invocationWord (encoding : Encoding Terminal problem) (n : ℕ) :
    List (Fin (problem.updateCount n) × problem.Update n) → List Terminal
  | [] => []
  | invocation :: rest =>
      encoding.update n invocation.1 invocation.2 ++
        invocationWord encoding n rest

theorem invocationWord_append
    (encoding : Encoding Terminal problem) (n : ℕ)
    (left right :
      List (Fin (problem.updateCount n) × problem.Update n)) :
    invocationWord encoding n (left ++ right) =
      invocationWord encoding n left ++ invocationWord encoding n right := by
  induction left with
  | nil => rfl
  | cons invocation rest ih =>
      simp [invocationWord, ih, List.append_assoc]

theorem invocationWord_ofFn
    (encoding : Encoding Terminal problem) (n : ℕ)
    (updates : Fin (problem.updateCount n) → problem.Update n) :
    invocationWord encoding n
        (List.ofFn fun index => (index, updates index)) =
      encoding.updateWord n updates := by
  have mapEquality :
      invocationWord encoding n
          (List.ofFn fun index => (index, updates index)) =
        ((List.ofFn fun index => (index, updates index)).map
          fun invocation =>
            encoding.update n invocation.1 invocation.2).flatten := by
    generalize
      (List.ofFn fun index => (index, updates index)) = invocations
    induction invocations with
    | nil => rfl
    | cons invocation rest ih =>
        simp [invocationWord, ih]
  rw [mapEquality]
  unfold Encoding.updateWord encodedUpdates
  congr 1
  simp [List.map_ofFn, Function.comp_def]

def runInvocations
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (encoding : Encoding Terminal problem) (n : ℕ) :
    (Fin stateCount × Scaffold (Fin workLabelCount) degree) →
    List (Fin (problem.updateCount n) × problem.Update n) →
      Fin stateCount × Scaffold (Fin workLabelCount) degree
  | configuration, [] => configuration
  | configuration, invocation :: rest =>
      runInvocations automaton encoding n
        (QueryOverlay.runFrom automaton configuration
          (encoding.update n invocation.1 invocation.2)) rest

theorem runInvocations_eq_runFrom
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (encoding : Encoding Terminal problem) (n : ℕ)
    (configuration : Fin stateCount ×
      Scaffold (Fin workLabelCount) degree)
    (invocations :
      List (Fin (problem.updateCount n) × problem.Update n)) :
    runInvocations automaton encoding n configuration invocations =
      QueryOverlay.runFrom automaton configuration
        (invocationWord encoding n invocations) := by
  induction invocations generalizing configuration with
  | nil => rfl
  | cons invocation rest ih =>
      rw [invocationWord, QueryOverlay.runFrom_append]
      exact ih _

noncomputable def compileUpdate
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing :
      CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (encoding : Encoding Terminal problem) (n : ℕ)
    (index : Fin (problem.updateCount n)) (value : problem.Update n) :
    BoundedUpdate wordBits
      (1 + encoding.updateBound n * stepReads degree radius)
      (1 + encoding.updateBound n * stepWrites degree) :=
  let symbols := encoding.update n index value
  { reads := updateReadBudget degree radius symbols
    writes := updateWriteBudget degree symbols
    program := compileUpdateBlock automaton packing symbols
    reads_le := by
      rw [updateReadBudget, blockBudget_eq]
      have lengthBound := encoding.update_length n index value
      simpa [Nat.add_comm] using Nat.add_le_add_left
        (Nat.mul_le_mul_right (stepReads degree radius) lengthBound) 1
    writes_le := by
      rw [updateWriteBudget, blockBudget_eq]
      have lengthBound := encoding.update_length n index value
      simpa [Nat.add_comm] using Nat.add_le_add_left
        (Nat.mul_le_mul_right (stepWrites degree) lengthBound) 1 }

noncomputable def compileFinalQuery
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing :
      CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (encoding : Encoding Terminal problem) (n : ℕ)
    (value : problem.Query n) :
    BoundedQuery wordBits
      (2 + encoding.queryBound n * viewBudget degree radius) :=
  let symbols := encoding.query n value
  { reads := countedQueryBudget degree radius symbols
    program := compileCountedQuery automaton packing symbols
    reads_le := by
      rw [countedQueryBudget, queryBudget_eq]
      have lengthBound := encoding.query_length n value
      have multiplied :=
        Nat.mul_le_mul_right (viewBudget degree radius) lengthBound
      dsimp only [symbols]
      calc
        1 + (encoding.query n value).length * viewBudget degree radius + 1 =
            2 + (encoding.query n value).length *
              viewBudget degree radius := by omega
        _ ≤ 2 + encoding.queryBound n * viewBudget degree radius :=
          Nat.add_le_add_left multiplied 2 }

structure CompiledState
    (packing :
      CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (memory : FiniteMemory wordBits)
    (configuration : Fin stateCount ×
      Scaffold (Fin workLabelCount) degree) : Type where
  graph : StableGraph stateCount workLabelCount maxNodes degree
  represents : packing.Represents memory graph
  relation : ConfigurationCorresponds graph configuration

noncomputable def preprocess
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing :
      CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (encoding : Encoding Terminal problem) (n : ℕ)
    (data : problem.Data n) : FiniteMemory wordBits :=
  if space : (encoding.pre n data).length + 1 ≤ maxNodes then
    let run := initialRunCorrespondence automaton
      (encoding.pre n data) space
    packing.encode run.1
  else
    fun _ => 0

noncomputable def preprocessingState
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing :
      CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (encoding : Encoding Terminal problem) (n : ℕ)
    (data : problem.Data n)
    (space : (encoding.pre n data).length + 1 ≤ maxNodes) :
    CompiledState packing (preprocess automaton packing encoding n data)
      (automaton.run (encoding.pre n data)) := by
  let run := initialRunCorrespondence automaton
    (encoding.pre n data) space
  have memoryEquality :
      preprocess automaton packing encoding n data =
        packing.encode run.1 := by
    simp [preprocess, space, run]
  refine
    { graph := run.1
      represents := ?_
      relation := run.2 }
  rw [memoryEquality]
  exact packing.encode_represents run.1

theorem preprocessingState_count
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing :
      CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (encoding : Encoding Terminal problem) (n : ℕ)
    (data : problem.Data n)
    (space : (encoding.pre n data).length + 1 ≤ maxNodes) :
    (preprocessingState automaton packing encoding n data space).graph.count =
      (encoding.pre n data).length + 1 := by
  unfold preprocessingState
  exact initialRunCorrespondence_count automaton (encoding.pre n data) space

noncomputable def compileInvocationState
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing :
      CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (encoding : Encoding Terminal problem) (n : ℕ) :
    (memory : FiniteMemory wordBits) →
    (configuration : Fin stateCount ×
      Scaffold (Fin workLabelCount) degree) →
    (current : CompiledState packing memory configuration) →
    (invocations :
      List (Fin (problem.updateCount n) × problem.Update n)) →
    (space :
      current.graph.count +
        (invocationWord encoding n invocations).length ≤ maxNodes) →
    { result : CompiledState packing
        (runUpdateList (compileUpdate automaton packing encoding n)
          memory invocations)
        (runInvocations automaton encoding n configuration invocations) //
      result.graph.count =
        current.graph.count +
          (invocationWord encoding n invocations).length }
  | _, _, current, [], _ => ⟨current, by simp [invocationWord]⟩
  | memory, configuration, current, invocation :: rest, space => by
      let symbols := encoding.update n invocation.1 invocation.2
      have normalized :
          current.graph.count + symbols.length +
              (invocationWord encoding n rest).length ≤ maxNodes := by
        simpa only [symbols, invocationWord, List.length_append,
          Nat.add_assoc] using space
      have blockSpace : current.graph.count + symbols.length ≤ maxNodes :=
        (Nat.le_add_right
          (current.graph.count + symbols.length)
          (invocationWord encoding n rest).length).trans normalized
      let nextRelation :=
        (runCorrespondence automaton current.relation symbols blockSpace).2
      let nextGraph :=
        (runCorrespondence automaton current.relation symbols blockSpace).1
      let nextMemory :=
        ((compileUpdateBlock automaton packing symbols).execute memory).memory
      have nextRepresents : packing.Represents nextMemory nextGraph :=
        compileUpdateBlock_represents automaton packing symbols memory
          current.graph configuration current.relation current.represents
          blockSpace
      have countEquality :
          nextGraph.count = current.graph.count + symbols.length :=
        runCorrespondence_count automaton current.relation symbols blockSpace
      have nextSpace :
          nextGraph.count +
              (invocationWord encoding n rest).length ≤ maxNodes := by
        rw [countEquality]
        exact normalized
      let nextState : CompiledState packing nextMemory
          (QueryOverlay.runFrom automaton configuration symbols) :=
        { graph := nextGraph
          represents := nextRepresents
          relation := nextRelation }
      let recursive := compileInvocationState automaton packing encoding n
        nextMemory
        (QueryOverlay.runFrom automaton configuration symbols)
        nextState rest nextSpace
      refine ⟨recursive.1, ?_⟩
      rw [recursive.2]
      change
        nextGraph.count + (invocationWord encoding n rest).length =
          current.graph.count +
            (invocationWord encoding n (invocation :: rest)).length
      rw [countEquality]
      simp only [invocationWord, List.length_append]
      dsimp only [symbols]
      omega

noncomputable def exactTransferAtDimension
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (packing :
      CountedPacking wordBits maxNodes stateCount workLabelCount degree)
    (encoding : Encoding Terminal problem)
    (decides : ∀ word, automaton.Accepts word ↔ encoding.language word)
    (n : ℕ)
    (capacity : ∀ data updates finalQuery,
      (encoding.word n data updates finalQuery).length + 1 ≤ maxNodes) :
    ExactStructure problem n wordBits
      (1 + encoding.updateBound n * stepReads degree radius)
      (1 + encoding.updateBound n * stepWrites degree)
      (2 + encoding.queryBound n * viewBudget degree radius) := by
  refine
    { preprocess := preprocess automaton packing encoding n
      update := compileUpdate automaton packing encoding n
      query := compileFinalQuery automaton packing encoding n
      correct := ?_ }
  intro data updates finalQuery
  let invocations :=
    List.ofFn fun index => (index, updates index)
  have wordCapacity := capacity data updates finalQuery
  have preSpace : (encoding.pre n data).length + 1 ≤ maxNodes := by
    simp only [Encoding.word, encodedWord, List.length_append] at wordCapacity
    omega
  let initial := preprocessingState automaton packing encoding n data preSpace
  have updateSpace :
      initial.graph.count +
          (invocationWord encoding n invocations).length ≤ maxNodes := by
    have initialCount := preprocessingState_count automaton packing encoding
      n data preSpace
    have invocationEquality :=
      invocationWord_ofFn encoding n updates
    unfold Encoding.updateWord at invocationEquality
    rw [initialCount, invocationEquality]
    simp only [Encoding.word, encodedWord, List.length_append] at wordCapacity
    omega
  let finalRun := compileInvocationState automaton packing encoding n
    (preprocess automaton packing encoding n data)
    (automaton.run (encoding.pre n data)) initial invocations updateSpace
  let final := finalRun.1
  have finalCount :
      final.graph.count =
        initial.graph.count +
          (invocationWord encoding n invocations).length := by
    exact finalRun.2
  have querySpace :
      final.graph.count + (encoding.query n finalQuery).length ≤ maxNodes := by
    rw [finalCount]
    have initialCount := preprocessingState_count automaton packing encoding
      n data preSpace
    have invocationEquality :=
      invocationWord_ofFn encoding n updates
    unfold Encoding.updateWord at invocationEquality
    rw [initialCount, invocationEquality]
    simp only [Encoding.word, encodedWord, List.length_append] at wordCapacity
    omega
  have queryCorrect' :
      ((compileCountedQuery automaton packing
        (encoding.query n finalQuery)).execute
        (runUpdates (compileUpdate automaton packing encoding n)
          (preprocess automaton packing encoding n data) updates)).result =
      decide ((QueryOverlay.runFrom automaton
        (runInvocations automaton encoding n
          (automaton.run (encoding.pre n data)) invocations)
        (encoding.query n finalQuery)).1 ∈ automaton.accepting) := by
    exact compileCountedQuery_correct automaton packing
      (encoding.query n finalQuery)
      (runUpdates (compileUpdate automaton packing encoding n)
        (preprocess automaton packing encoding n data) updates)
      final.graph
      (runInvocations automaton encoding n
        (automaton.run (encoding.pre n data)) invocations)
      final.relation final.represents querySpace
  change
    ((compileCountedQuery automaton packing
      (encoding.query n finalQuery)).execute
      (runUpdates (compileUpdate automaton packing encoding n)
        (preprocess automaton packing encoding n data) updates)).result =
      problem.answer n data updates finalQuery
  rw [queryCorrect']
  have invocationEquality := invocationWord_ofFn encoding n updates
  have executionEquality :
      QueryOverlay.runFrom automaton
          (runInvocations automaton encoding n
            (automaton.run (encoding.pre n data)) invocations)
          (encoding.query n finalQuery) =
        automaton.run (encoding.word n data updates finalQuery) := by
    rw [runInvocations_eq_runFrom, invocationEquality]
    unfold Encoding.updateWord
    rw [← QueryOverlay.runFrom_append]
    rw [← QueryOverlay.runFrom_initial automaton (encoding.pre n data)]
    rw [← QueryOverlay.runFrom_append]
    rw [QueryOverlay.runFrom_initial]
    simp [Encoding.word, encodedWord, List.append_assoc]
  have answerIff :
      (QueryOverlay.runFrom automaton
          (runInvocations automaton encoding n
            (automaton.run (encoding.pre n data)) invocations)
          (encoding.query n finalQuery)).1 ∈ automaton.accepting ↔
        problem.answer n data updates finalQuery = true := by
    rw [executionEquality]
    exact (decides _).trans (encoding.correct n data updates finalQuery)
  cases answerValue : problem.answer n data updates finalQuery <;>
    simp_all

noncomputable def transferAtDimension
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (encoding : Encoding Terminal problem)
    (decides : ∀ word, automaton.Accepts word ↔ encoding.language word)
    (n : ℕ) :
    ExactStructure problem n
      (GenericPackingBounds.wordBits stateCount workLabelCount degree
        encoding.polynomialConstant encoding.polynomialExponent n)
      (1 + encoding.updateBound n * stepReads degree radius)
      (1 + encoding.updateBound n * stepWrites degree)
      (2 + encoding.queryBound n * viewBudget degree radius) :=
  exactTransferAtDimension automaton
    (GenericPackingBounds.countedPacking stateCount workLabelCount degree
      encoding.polynomialConstant encoding.polynomialExponent n)
    encoding decides n
    (GenericPackingBounds.encodedWord_nodes_fit encoding n)

theorem genericTransferTheorem
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (encoding : Encoding Terminal problem)
    (decides : ∀ word, automaton.Accepts word ↔ encoding.language word) :
    let scale :=
      GenericPackingBounds.wordScale stateCount workLabelCount degree
        encoding.polynomialConstant encoding.polynomialExponent
    0 < scale ∧
      (∀ n,
        Nonempty
          (ExactStructure problem n
            (scale * GenericPackingBounds.logWidth n)
            (1 + encoding.updateBound n * stepReads degree radius)
            (1 + encoding.updateBound n * stepWrites degree)
            (2 + encoding.queryBound n * viewBudget degree radius))) ∧
      (∀ n,
        2 ^ (scale * GenericPackingBounds.logWidth n) ≤
          4 ^ scale * (n + 1) ^ scale) ∧
      (∀ n,
        (1 + encoding.updateBound n * stepReads degree radius) +
            (1 + encoding.updateBound n * stepWrites degree) ≤
          (stepReads degree radius + stepWrites degree + 2) *
            encoding.updateBound n) ∧
      (∀ n,
        2 + encoding.queryBound n * viewBudget degree radius ≤
          (viewBudget degree radius + 2) * encoding.queryBound n) := by
  dsimp only
  refine ⟨by unfold GenericPackingBounds.wordScale; omega, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨transferAtDimension automaton encoding decides n⟩
  · intro n
    exact GenericPackingBounds.addressSpace_polynomial_bound
      stateCount workLabelCount degree encoding.polynomialConstant
        encoding.polynomialExponent n
  · intro n
    have positive := encoding.updateBound_pos n
    nlinarith
  · intro n
    have positive := encoding.queryBound_pos n
    nlinarith

end PegSeparation.Reduction.GenericTransfer
