import PegSeparation.CFLNotPEG.LowerBound.Chronogram
import PegSeparation.CFLNotPEG.Reduction.SCAToCellProbe


namespace PegSeparation.LowerBound.Staticization

open PegSeparation.CellProbe
open PegSeparation.Reduction


structure BatchExecution (wordBits : ℕ) where
  memory : SCAToCellProbe.FiniteMemory wordBits
  readTrace : List (Address wordBits)
  writes : List (SCAToCellProbe.WriteEntry wordBits)

def executeBatch {wordBits reads writes : ℕ}
    (initial : SCAToCellProbe.FiniteMemory wordBits) :
    List (SCAToCellProbe.UpdateProgram wordBits Unit reads writes) →
      BatchExecution wordBits
  | [] => { memory := initial, readTrace := [], writes := [] }
  | program :: rest =>
      let first := program.execute initial
      let later := executeBatch first.memory rest
      { memory := later.memory
        readTrace := first.readTrace ++ later.readTrace
        writes := first.writes ++ later.writes }

theorem replayWrites_append {wordBits : ℕ}
    (initial : SCAToCellProbe.FiniteMemory wordBits)
    (first later : List (SCAToCellProbe.WriteEntry wordBits)) :
    SCAToCellProbe.replayWrites initial (first ++ later) =
      SCAToCellProbe.replayWrites
        (SCAToCellProbe.replayWrites initial first) later := by
  induction first generalizing initial with
  | nil => rfl
  | cons write rest ih =>
      simpa only [List.cons_append, SCAToCellProbe.replayWrites] using
        ih (Function.update initial write.address write.value)

@[simp] theorem executeBatch_nil {wordBits reads writes : ℕ}
    (initial : SCAToCellProbe.FiniteMemory wordBits) :
    executeBatch (reads := reads) (writes := writes) initial [] =
      { memory := initial, readTrace := [], writes := [] } := rfl

theorem executeBatch_memory_eq_replay {wordBits reads writes : ℕ}
    (initial : SCAToCellProbe.FiniteMemory wordBits)
    (programs : List (SCAToCellProbe.UpdateProgram wordBits Unit reads writes)) :
    (executeBatch initial programs).memory =
      SCAToCellProbe.replayWrites initial (executeBatch initial programs).writes := by
  induction programs generalizing initial with
  | nil => rfl
  | cons program rest ih =>
      simp only [executeBatch]
      rw [ih]
      rw [SCAToCellProbe.UpdateProgram.execute_memory_eq_replay]
      rw [← replayWrites_append]

theorem executeBatch_readTrace_length {wordBits reads writes : ℕ}
    (initial : SCAToCellProbe.FiniteMemory wordBits)
    (programs : List (SCAToCellProbe.UpdateProgram wordBits Unit reads writes)) :
    (executeBatch initial programs).readTrace.length = programs.length * reads := by
  induction programs generalizing initial with
  | nil => simp [executeBatch]
  | cons program rest ih =>
      simp [executeBatch,
        SCAToCellProbe.UpdateProgram.execute_readTrace_length, ih,
        Nat.add_mul, Nat.add_comm]

theorem executeBatch_writes_length {wordBits reads writes : ℕ}
    (initial : SCAToCellProbe.FiniteMemory wordBits)
    (programs : List (SCAToCellProbe.UpdateProgram wordBits Unit reads writes)) :
    (executeBatch initial programs).writes.length = programs.length * writes := by
  induction programs generalizing initial with
  | nil => simp [executeBatch]
  | cons program rest ih =>
      simp [executeBatch,
        SCAToCellProbe.UpdateProgram.execute_writes_length, ih,
        Nat.add_mul, Nat.add_comm]


def addressSlot {count : ℕ} (index : Fin count) : Fin (count + count) :=
  Fin.castAdd count index

def valueSlot {count : ℕ} (index : Fin count) : Fin (count + count) :=
  Fin.natAdd count index

def encodeWriteCache {wordBits count : ℕ}
    (trace : List (SCAToCellProbe.WriteEntry wordBits))
    (hlen : trace.length = count) : Fin (count + count) → Word wordBits :=
  Fin.addCases
    (fun index => (trace.get (Fin.cast hlen.symm index)).address)
    (fun index => (trace.get (Fin.cast hlen.symm index)).value)

@[simp] theorem encodeWriteCache_addressSlot {wordBits count : ℕ}
    (trace : List (SCAToCellProbe.WriteEntry wordBits))
    (hlen : trace.length = count) (index : Fin count) :
    encodeWriteCache trace hlen (addressSlot index) =
      (trace.get (Fin.cast hlen.symm index)).address := by
  simp only [encodeWriteCache, addressSlot, Fin.addCases_left]

@[simp] theorem encodeWriteCache_valueSlot {wordBits count : ℕ}
    (trace : List (SCAToCellProbe.WriteEntry wordBits))
    (hlen : trace.length = count) (index : Fin count) :
    encodeWriteCache trace hlen (valueSlot index) =
      (trace.get (Fin.cast hlen.symm index)).value := by
  simp only [encodeWriteCache, valueSlot, Fin.addCases_right]

def decodeWriteCache {wordBits count : ℕ}
    (cache : Fin (count + count) → Word wordBits) :
    List (SCAToCellProbe.WriteEntry wordBits) :=
  List.ofFn fun index =>
    { address := cache (addressSlot index)
      value := cache (valueSlot index) }

theorem decodeWriteCache_length {wordBits count : ℕ}
    (cache : Fin (count + count) → Word wordBits) :
    (decodeWriteCache cache).length = count := by
  simp [decodeWriteCache]

theorem decode_encodeWriteCache {wordBits count : ℕ}
    (trace : List (SCAToCellProbe.WriteEntry wordBits))
    (hlen : trace.length = count) :
    decodeWriteCache (encodeWriteCache trace hlen) = trace := by
  apply List.ext_get
  · simp [decodeWriteCache, hlen]
  · intro index hleft hright
    simp only [decodeWriteCache, List.get_ofFn]
    cases hentry : trace.get ⟨index, hright⟩ with
    | mk address value =>
      congr 1
      · rw [encodeWriteCache_addressSlot]
        convert congrArg SCAToCellProbe.WriteEntry.address hentry using 1
        congr 2
      · rw [encodeWriteCache_valueSlot]
        convert congrArg SCAToCellProbe.WriteEntry.value hentry using 1
        congr 2


def cachedQueryTree {wordBits : ℕ}
    (lookup : Address wordBits → Option (Word wordBits)) :
    {probes : ℕ} → SCAToCellProbe.ReadProgram wordBits Bool probes →
      QueryTree wordBits
  | _, .done answer => .answer answer
  | _, .probe address next =>
      match lookup address with
      | some value => cachedQueryTree lookup (next value)
      | none => .probe address (fun value => cachedQueryTree lookup (next value))

theorem cachedQueryTree_run {wordBits probes : ℕ}
    (preMemory : SCAToCellProbe.FiniteMemory wordBits)
    (cacheWrites : List (SCAToCellProbe.WriteEntry wordBits))
    (program : SCAToCellProbe.ReadProgram wordBits Bool probes) :
    (cachedQueryTree (SCAToCellProbe.lastWritten cacheWrites) program).run
        preMemory =
      ((program.execute
          (SCAToCellProbe.readWithCache preMemory cacheWrites)).result,
        (program.execute
          (SCAToCellProbe.readWithCache preMemory cacheWrites)).trace.filter
            fun address =>
              (SCAToCellProbe.lastWritten cacheWrites address).isNone) := by
  induction program with
  | done => rfl
  | @probe remaining address next ih =>
      cases hcache : SCAToCellProbe.lastWritten cacheWrites address with
      | none =>
          simp only [cachedQueryTree, hcache, QueryTree.run,
            SCAToCellProbe.ReadProgram.execute, List.filter_cons]
          rw [ih (preMemory address)]
          simp [SCAToCellProbe.readWithCache, hcache]
      | some value =>
          simp only [cachedQueryTree, hcache,
            SCAToCellProbe.ReadProgram.execute, List.filter_cons]
          rw [ih value]
          simp [SCAToCellProbe.readWithCache, hcache]


def writtenAddresses {wordBits : ℕ}
    (trace : List (SCAToCellProbe.WriteEntry wordBits)) :
    Finset (Address wordBits) :=
  (trace.map SCAToCellProbe.WriteEntry.address).toFinset

@[simp] theorem mem_writtenAddresses {wordBits : ℕ}
    {trace : List (SCAToCellProbe.WriteEntry wordBits)}
    {address : Address wordBits} :
    address ∈ writtenAddresses trace ↔
      ∃ write ∈ trace, write.address = address := by
  simp [writtenAddresses]

theorem writtenAddresses_card_le_length {wordBits : ℕ}
    (trace : List (SCAToCellProbe.WriteEntry wordBits)) :
    (writtenAddresses trace).card ≤ trace.length := by
  simpa [writtenAddresses] using
    List.toFinset_card_le (trace.map SCAToCellProbe.WriteEntry.address)

theorem lastWritten_eq_none_iff {wordBits : ℕ}
    (trace : List (SCAToCellProbe.WriteEntry wordBits))
    (address : Address wordBits) :
    SCAToCellProbe.lastWritten trace address = none ↔
      address ∉ writtenAddresses trace := by
  induction trace with
  | nil => simp [SCAToCellProbe.lastWritten, writtenAddresses]
  | cons write rest ih =>
      rw [show writtenAddresses (write :: rest) =
          insert write.address (writtenAddresses rest) by
        simp [writtenAddresses]]
      cases hlast : SCAToCellProbe.lastWritten rest address with
      | some value =>
          have hmem : address ∈ writtenAddresses rest := by
            by_contra hnot
            exact Option.some_ne_none value
              (hlast.symm.trans (ih.mpr hnot))
          simp [SCAToCellProbe.lastWritten, hlast, hmem]
      | none =>
          have hnot : address ∉ writtenAddresses rest :=
            ih.mp hlast
          by_cases heq : write.address = address
          · simp [SCAToCellProbe.lastWritten, hlast, heq]
          · simp [SCAToCellProbe.lastWritten, hlast, heq,
              Ne.symm heq, hnot]

structure PhasedProgram (Input Query : Type)
    (wordBits updateReads updateWrites queryProbes targetUpdates : ℕ) where
  initialMemory : SCAToCellProbe.FiniteMemory wordBits
  prehistory :
    List (SCAToCellProbe.UpdateProgram wordBits Unit updateReads updateWrites)
  target : Input →
    List (SCAToCellProbe.UpdateProgram wordBits Unit updateReads updateWrites)
  target_length : ∀ input, (target input).length = targetUpdates
  recent :
    List (SCAToCellProbe.UpdateProgram wordBits Unit updateReads updateWrites)
  queryProgram : Query →
    SCAToCellProbe.ReadProgram wordBits Bool queryProbes

namespace PhasedProgram

variable {Input Query : Type}
  {wordBits updateReads updateWrites queryProbes targetUpdates : ℕ}

def prehistoryExecution
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates) : BatchExecution wordBits :=
  executeBatch program.initialMemory program.prehistory

def targetExecution
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (input : Input) : BatchExecution wordBits :=
  executeBatch program.prehistoryExecution.memory (program.target input)

def recentExecution
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (input : Input) : BatchExecution wordBits :=
  executeBatch (program.targetExecution input).memory program.recent

def queryExecution
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (input : Input) (query : Query) : SCAToCellProbe.ReadExecution wordBits Bool :=
  (program.queryProgram query).execute (program.recentExecution input).memory

theorem target_writes_length
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (input : Input) :
    (program.targetExecution input).writes.length =
      targetUpdates * updateWrites := by
  rw [targetExecution, executeBatch_writes_length, program.target_length]

theorem recent_writes_length
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (input : Input) :
    (program.recentExecution input).writes.length =
      program.recent.length * updateWrites := by
  exact executeBatch_writes_length _ _

theorem target_memory_eq_readWithCache
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (input : Input) (address : Address wordBits) :
    (program.targetExecution input).memory address =
      SCAToCellProbe.readWithCache program.prehistoryExecution.memory
        (program.targetExecution input).writes address := by
  unfold targetExecution
  rw [executeBatch_memory_eq_replay]
  exact SCAToCellProbe.replayWrites_apply _ _ _

theorem recent_memory_eq_readWithCache
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (input : Input) (address : Address wordBits) :
    (program.recentExecution input).memory address =
      SCAToCellProbe.readWithCache (program.targetExecution input).memory
        (program.recentExecution input).writes address := by
  unfold recentExecution
  rw [executeBatch_memory_eq_replay]
  exact SCAToCellProbe.replayWrites_apply _ _ _

end PhasedProgram


def toStaticStructure {Input Query : Type}
    {wordBits updateReads updateWrites queryProbes targetUpdates : ℕ}
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates) :
    StaticStructure Input Query wordBits
      ((program.recent.length * updateWrites) +
        (program.recent.length * updateWrites))
      (targetUpdates * updateWrites) where
  preMemory := program.prehistoryExecution.memory
  updatedAddresses := fun input =>
    writtenAddresses (program.targetExecution input).writes
  updatedWord := fun input => (program.targetExecution input).memory
  updateBound := by
    intro input
    exact (writtenAddresses_card_le_length _).trans_eq
      (program.target_writes_length input)
  cache := fun input =>
    encodeWriteCache (program.recentExecution input).writes
      (program.recent_writes_length input)
  queryAlgorithm := fun query cache =>
    cachedQueryTree
      (SCAToCellProbe.lastWritten (decodeWriteCache cache))
      (program.queryProgram query)

namespace PhasedProgram

variable {Input Query : Type}
  {wordBits updateReads updateWrites queryProbes targetUpdates : ℕ}

theorem static_memory_eq_target
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (input : Input) :
    (toStaticStructure program).memory input =
      (program.targetExecution input).memory := by
  funext address
  unfold StaticStructure.memory
  change
    (if address ∈ writtenAddresses (program.targetExecution input).writes then
        (program.targetExecution input).memory address
      else program.prehistoryExecution.memory address) =
      (program.targetExecution input).memory address
  by_cases hwritten :
      address ∈ writtenAddresses (program.targetExecution input).writes
  · simp [hwritten]
  · simp only [hwritten, ↓reduceIte]
    rw [program.target_memory_eq_readWithCache input address]
    simp [SCAToCellProbe.readWithCache,
      (lastWritten_eq_none_iff _ _).mpr hwritten]

theorem decode_static_cache
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (input : Input) :
    decodeWriteCache ((toStaticStructure program).cache input) =
      (program.recentExecution input).writes := by
  simpa [toStaticStructure] using
    decode_encodeWriteCache (program.recentExecution input).writes
      (program.recent_writes_length input)

theorem static_execute_eq
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (input : Input) (query : Query) :
    (toStaticStructure program).execute input query =
      ((program.queryExecution input query).result,
        (program.queryExecution input query).trace.filter fun address =>
          (SCAToCellProbe.lastWritten
            (program.recentExecution input).writes address).isNone) := by
  unfold StaticStructure.execute
  change
    (cachedQueryTree
        (SCAToCellProbe.lastWritten
          (decodeWriteCache ((toStaticStructure program).cache input)))
        (program.queryProgram query)).run
      ((toStaticStructure program).memory input) = _
  rw [program.decode_static_cache input]
  rw [cachedQueryTree_run]
  rw [program.static_memory_eq_target input]
  have hmemory :
      SCAToCellProbe.readWithCache (program.targetExecution input).memory
          (program.recentExecution input).writes =
        (program.recentExecution input).memory := by
    funext address
    exact (program.recent_memory_eq_readWithCache input address).symm
  rw [hmemory]
  rfl

theorem static_answer_eq
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (input : Input) (query : Query) :
    (toStaticStructure program).answer input query =
      (program.queryExecution input query).result := by
  exact congrArg Prod.fst (program.static_execute_eq input query)

theorem static_probeTrace_eq
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (input : Input) (query : Query) :
    (toStaticStructure program).probeTrace input query =
      (program.queryExecution input query).trace.filter fun address =>
        (SCAToCellProbe.lastWritten
          (program.recentExecution input).writes address).isNone := by
  exact congrArg Prod.snd (program.static_execute_eq input query)

theorem static_totalProbes_le
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (input : Input) (query : Query) :
    ((toStaticStructure program).probeTrace input query).length ≤
      queryProbes := by
  rw [program.static_probeTrace_eq input query]
  refine (List.length_filter_le _ _).trans_eq ?_
  exact SCAToCellProbe.ReadProgram.execute_trace_length _ _

theorem static_solves
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (problem : BinaryProblem Input Query)
    (hcorrect : ∀ input query,
      (program.queryExecution input query).result =
        problem.value query input) :
    CellProbe.StaticStructure.Solves (toStaticStructure program) problem := by
  intro input query
  rw [program.static_answer_eq input query]
  exact hcorrect input query

end PhasedProgram


theorem countP_filter {Alpha : Type} (items : List Alpha)
    (keep count : Alpha → Prop) [DecidablePred keep] [DecidablePred count]
    [DecidablePred fun item => keep item ∧ count item] :
    (items.filter keep).countP count =
      items.countP fun item => keep item ∧ count item := by
  rw [List.countP_filter]
  apply List.countP_congr
  intro item _
  simp [and_comm]

def targetWriterProbeCount {wordBits : ℕ}
    (queryTrace : List (Address wordBits))
    (targetWrites recentWrites : List (SCAToCellProbe.WriteEntry wordBits)) : ℕ :=
  queryTrace.countP fun address =>
    Chronogram.staticLastWriter (writtenAddresses targetWrites)
      (writtenAddresses recentWrites) address = .target

namespace PhasedProgram

variable {Input Query : Type}
  {wordBits updateReads updateWrites queryProbes targetUpdates : ℕ}

theorem static_updatedProbeCount_eq_targetWriterProbeCount
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (input : Input) (query : Query) :
    (toStaticStructure program).updatedProbeCount input query =
      targetWriterProbeCount (program.queryExecution input query).trace
        (program.targetExecution input).writes
        (program.recentExecution input).writes := by
  unfold StaticStructure.updatedProbeCount
  rw [program.static_probeTrace_eq input query]
  rw [List.countP_filter]
  unfold targetWriterProbeCount
  apply List.countP_congr
  intro address _
  simp [toStaticStructure, lastWritten_eq_none_iff,
    Chronogram.staticLastWriter_eq_target]

theorem expectedUpdatedProbes_eq_targetWriterProbeCount
    [Fintype Input] [Fintype Query]
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    (toStaticStructure program).expectedUpdatedProbes
        inputDistribution queryDistribution =
      ∑ input, inputDistribution.mass input *
        ∑ query, queryDistribution.mass query *
          targetWriterProbeCount (program.queryExecution input query).trace
            (program.targetExecution input).writes
            (program.recentExecution input).writes := by
  unfold CellProbe.StaticStructure.expectedUpdatedProbes
  simp_rw [program.static_updatedProbeCount_eq_targetWriterProbeCount]

theorem expectedTotalProbes_le
    [Fintype Input] [Fintype Query]
    (program : PhasedProgram Input Query wordBits updateReads updateWrites
      queryProbes targetUpdates)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    (toStaticStructure program).expectedTotalProbes
        inputDistribution queryDistribution ≤ queryProbes := by
  unfold CellProbe.StaticStructure.expectedTotalProbes
  calc
    (∑ input, inputDistribution.mass input *
        ∑ query, queryDistribution.mass query *
          ((toStaticStructure program).probeTrace input query).length) ≤
        ∑ input, inputDistribution.mass input *
          ∑ query, queryDistribution.mass query * (queryProbes : ℝ) := by
      apply Finset.sum_le_sum
      intro input _
      apply mul_le_mul_of_nonneg_left _
        (inputDistribution.mass_nonnegative input)
      apply Finset.sum_le_sum
      intro query _
      apply mul_le_mul_of_nonneg_left _
        (queryDistribution.mass_nonnegative query)
      exact_mod_cast program.static_totalProbes_le input query
    _ = queryProbes := by
      have hquery :
          (∑ query, queryDistribution.mass query * (queryProbes : ℝ)) =
            queryProbes := by
        rw [← Finset.sum_mul]
        rw [queryDistribution.mass_sum]
        simp
      rw [hquery]
      rw [← Finset.sum_mul]
      rw [inputDistribution.mass_sum]
      simp

end PhasedProgram


def newestWriter {Epoch : Type} {wordBits : ℕ}
    (newestFirst : List Epoch)
    (writes : Epoch → List (SCAToCellProbe.WriteEntry wordBits))
    (address : Address wordBits) : Chronogram.WriterBucket Epoch :=
  match newestFirst with
  | [] => .prehistory
  | epoch :: older =>
      if address ∈ writtenAddresses (writes epoch) then .epoch epoch
      else newestWriter older writes address

def writtenByEpochs {Epoch : Type} {wordBits : ℕ}
    (epochs : List Epoch)
    (writes : Epoch → List (SCAToCellProbe.WriteEntry wordBits)) :
    Finset (Address wordBits) :=
  match epochs with
  | [] => ∅
  | epoch :: rest =>
      writtenAddresses (writes epoch) ∪ writtenByEpochs rest writes

@[simp] theorem newestWriter_nil {Epoch : Type} {wordBits : ℕ}
    (writes : Epoch → List (SCAToCellProbe.WriteEntry wordBits))
    (address : Address wordBits) :
    newestWriter [] writes address = .prehistory := rfl

@[simp] theorem writtenByEpochs_nil {Epoch : Type} {wordBits : ℕ}
    (writes : Epoch → List (SCAToCellProbe.WriteEntry wordBits)) :
    writtenByEpochs [] writes = ∅ := rfl

@[simp] theorem writtenByEpochs_cons {Epoch : Type} {wordBits : ℕ}
    (epoch : Epoch) (rest : List Epoch)
    (writes : Epoch → List (SCAToCellProbe.WriteEntry wordBits)) :
    writtenByEpochs (epoch :: rest) writes =
      writtenAddresses (writes epoch) ∪ writtenByEpochs rest writes := rfl

theorem newestWriter_eq_prehistory_iff {Epoch : Type} {wordBits : ℕ}
    (epochs : List Epoch)
    (writes : Epoch → List (SCAToCellProbe.WriteEntry wordBits))
    (address : Address wordBits) :
    newestWriter epochs writes address = .prehistory ↔
      address ∉ writtenByEpochs epochs writes := by
  induction epochs with
  | nil => simp
  | cons epoch rest ih =>
      by_cases hwritten : address ∈ writtenAddresses (writes epoch)
      · simp [newestWriter, writtenByEpochs, hwritten]
      · simp [newestWriter, writtenByEpochs, hwritten, ih]

theorem newestWriter_epoch_mem {Epoch : Type} {wordBits : ℕ}
    (epochs : List Epoch)
    (writes : Epoch → List (SCAToCellProbe.WriteEntry wordBits))
    (address : Address wordBits) (target : Epoch)
    (hwriter : newestWriter epochs writes address = .epoch target) :
    target ∈ epochs := by
  induction epochs with
  | nil => cases hwriter
  | cons epoch rest ih =>
      by_cases hwritten : address ∈ writtenAddresses (writes epoch)
      · simp only [newestWriter, hwritten, ↓reduceIte] at hwriter
        exact List.mem_cons.mpr
          (Or.inl (Chronogram.WriterBucket.epoch.inj hwriter).symm)
      · simp only [newestWriter, hwritten, ↓reduceIte] at hwriter
        exact List.mem_cons.mpr (Or.inr (ih hwriter))

theorem newestWriter_split_eq_target_iff
    {Epoch : Type} {wordBits : ℕ}
    (newer older : List Epoch) (target : Epoch)
    (writes : Epoch → List (SCAToCellProbe.WriteEntry wordBits))
    (horder : (newer ++ target :: older).Nodup)
    (address : Address wordBits) :
    newestWriter (newer ++ target :: older) writes address = .epoch target ↔
      address ∈ writtenAddresses (writes target) ∧
        address ∉ writtenByEpochs newer writes := by
  induction newer with
  | nil =>
      have htargetOlder : target ∉ older := by
        simpa using (List.nodup_cons.mp horder).1
      by_cases htarget : address ∈ writtenAddresses (writes target)
      · simp [newestWriter, writtenByEpochs, htarget]
      · have hne : newestWriter older writes address ≠ .epoch target := by
          intro heq
          exact htargetOlder (newestWriter_epoch_mem older writes address target heq)
        simp [newestWriter, writtenByEpochs, htarget, hne]
  | cons epoch rest ih =>
      have htail : (rest ++ target :: older).Nodup := by
        exact (List.nodup_cons.mp horder).2
      have hepochTarget : epoch ≠ target := by
        intro heq
        subst epoch
        have hnot : target ∉ rest ++ target :: older :=
          (List.nodup_cons.mp horder).1
        exact hnot (by simp)
      by_cases hepoch : address ∈ writtenAddresses (writes epoch)
      · simp [List.cons_append, newestWriter, writtenByEpochs,
          hepoch, hepochTarget]
      · simpa [List.cons_append, newestWriter, writtenByEpochs, hepoch] using
          ih htail

theorem newestWriter_split_iff_staticLastWriter_target
    {Epoch : Type} {wordBits : ℕ}
    (newer older : List Epoch) (target : Epoch)
    (writes : Epoch → List (SCAToCellProbe.WriteEntry wordBits))
    (horder : (newer ++ target :: older).Nodup)
    (address : Address wordBits) :
    newestWriter (newer ++ target :: older) writes address = .epoch target ↔
      Chronogram.staticLastWriter (writtenAddresses (writes target))
        (writtenByEpochs newer writes) address = .target := by
  rw [newestWriter_split_eq_target_iff newer older target writes horder address]
  exact Chronogram.staticLastWriter_eq_target.symm

def probeOccurrences {wordBits : ℕ}
    (trace : List (Address wordBits)) : Finset ℕ :=
  Finset.range trace.length

@[simp] theorem probeOccurrences_card {wordBits : ℕ}
    (trace : List (Address wordBits)) :
    (probeOccurrences trace).card = trace.length := by
  simp [probeOccurrences]

def occurrenceLastWriter {Epoch : Type} {wordBits : ℕ}
    (newestFirst : List Epoch)
    (writes : Epoch → List (SCAToCellProbe.WriteEntry wordBits))
    (trace : List (Address wordBits)) (index : ℕ) :
    Chronogram.WriterBucket Epoch :=
  if hindex : index < trace.length then
    newestWriter newestFirst writes (trace.get ⟨index, hindex⟩)
  else
    .prehistory

theorem occurrenceLastWriter_of_mem {Epoch : Type} {wordBits : ℕ}
    (newestFirst : List Epoch)
    (writes : Epoch → List (SCAToCellProbe.WriteEntry wordBits))
    (trace : List (Address wordBits)) (index : ℕ)
    (hindex : index ∈ probeOccurrences trace) :
    occurrenceLastWriter newestFirst writes trace index =
      newestWriter newestFirst writes
        (trace.get ⟨index, by simpa [probeOccurrences] using hindex⟩) := by
  simp only [probeOccurrences, Finset.mem_range] at hindex
  simp [occurrenceLastWriter, hindex]

theorem exists_cheap_actual_epoch_on_average
    {Sample Epoch : Type} [DecidableEq Epoch] {wordBits : ℕ}
    (samples : Finset Sample)
    (queryTrace : Sample → List (Address wordBits))
    (newestFirst : List Epoch)
    (epochWrites : Sample → Epoch →
      List (SCAToCellProbe.WriteEntry wordBits))
    (epochs : Finset Epoch) (hne : epochs.Nonempty) :
    ∃ epoch ∈ epochs,
      (∑ sample ∈ samples,
          (Chronogram.epochOccurrences
            (probeOccurrences (queryTrace sample))
            (occurrenceLastWriter newestFirst (epochWrites sample)
              (queryTrace sample)) epoch).card) * epochs.card ≤
        ∑ sample ∈ samples, (queryTrace sample).length := by
  simpa only [probeOccurrences_card] using
    Chronogram.exists_cheap_epoch_on_average samples
      (fun sample => probeOccurrences (queryTrace sample))
      (fun sample => occurrenceLastWriter newestFirst (epochWrites sample)
        (queryTrace sample)) epochs hne

end PegSeparation.LowerBound.Staticization
