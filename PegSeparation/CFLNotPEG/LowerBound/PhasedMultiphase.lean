import PegSeparation.CFLNotPEG.Reduction.MultiphaseModel
import PegSeparation.CFLNotPEG.LowerBound.Staticization
import PegSeparation.CFLNotPEG.LowerBound.EpochGeometry
import PegSeparation.CFLNotPEG.LowerBound.BlockAdapter


namespace PegSeparation.LowerBound.PhasedMultiphase

open PegSeparation
open PegSeparation.Witness
open PegSeparation.Reduction
open PegSeparation.CellProbe

abbrev F2 := RandomCoherence.F2
abbrev F2Vec := RandomCoherence.F2Vec
abbrev RowMatrix := RandomCoherence.RowMatrix
abbrev BitVector := MultiphaseModel.BitVector
abbrev IPMatrix := MultiphaseModel.IPMatrix


def InTarget (n gamma i : ℕ) (coordinate : Fin n) : Prop :=
  EpochGeometry.epochStart n gamma i ≤ coordinate.val ∧
    coordinate.val < EpochGeometry.epochEnd n gamma i

instance instDecidablePredInTarget (n gamma i : ℕ) :
    DecidablePred (InTarget n gamma i) := by
  intro coordinate
  unfold InTarget
  infer_instance

abbrev ContiguousTarget (n gamma i : ℕ) :=
  {coordinate : Fin n // InTarget n gamma i coordinate}

abbrev ContiguousOutside (n gamma i : ℕ) :=
  {coordinate : Fin n // ¬ InTarget n gamma i coordinate}

noncomputable instance instFintypeContiguousTarget (n gamma i : ℕ) :
    Fintype (ContiguousTarget n gamma i) :=
  Fintype.ofFinite _

noncomputable instance instFintypeContiguousOutside (n gamma i : ℕ) :
    Fintype (ContiguousOutside n gamma i) :=
  Fintype.ofFinite _

def targetEquiv {n gamma i : ℕ}
    (hfit : EpochGeometry.epochEnd n gamma i ≤ n) :
    Fin (gamma ^ i) ≃ ContiguousTarget n gamma i where
  toFun coordinate :=
    ⟨EpochGeometry.targetEmbedding n gamma i hfit coordinate, by
      change
        EpochGeometry.epochStart n gamma i ≤
            EpochGeometry.epochStart n gamma i + coordinate.val ∧
          EpochGeometry.epochStart n gamma i + coordinate.val <
            EpochGeometry.epochStart n gamma i + gamma ^ i
      omega⟩
  invFun coordinate :=
    ⟨coordinate.val.val - EpochGeometry.epochStart n gamma i, by
      have hstart := coordinate.property.1
      have hend := coordinate.property.2
      change EpochGeometry.epochStart n gamma i ≤ coordinate.val.val at hstart
      change coordinate.val.val <
        EpochGeometry.epochStart n gamma i + gamma ^ i at hend
      omega⟩
  left_inv coordinate := by
    apply Fin.ext
    change
      (EpochGeometry.epochStart n gamma i + coordinate.val) -
          EpochGeometry.epochStart n gamma i = coordinate.val
    omega
  right_inv coordinate := by
    apply Subtype.ext
    apply Fin.ext
    change
      EpochGeometry.epochStart n gamma i +
          (coordinate.val.val - EpochGeometry.epochStart n gamma i) =
        coordinate.val.val
    exact Nat.add_sub_of_le coordinate.property.1

def contiguousSplit {n gamma i : ℕ}
    (hfit : EpochGeometry.epochEnd n gamma i ≤ n) :
    Fin n ≃ Sum (Fin (gamma ^ i)) (ContiguousOutside n gamma i) :=
  ((Equiv.sumCompl (InTarget n gamma i)).symm).trans
    (Equiv.sumCongr (targetEquiv hfit).symm
      (Equiv.refl (ContiguousOutside n gamma i)))

theorem targetEmbedding_inTarget {n gamma i : ℕ}
    (hfit : EpochGeometry.epochEnd n gamma i ≤ n)
    (coordinate : Fin (gamma ^ i)) :
    InTarget n gamma i
      (EpochGeometry.targetEmbedding n gamma i hfit coordinate) := by
  change
    EpochGeometry.epochStart n gamma i ≤
        EpochGeometry.epochStart n gamma i + coordinate.val ∧
      EpochGeometry.epochStart n gamma i + coordinate.val <
        EpochGeometry.epochStart n gamma i + gamma ^ i
  omega

@[simp] theorem contiguousSplit_targetEmbedding {n gamma i : ℕ}
    (hfit : EpochGeometry.epochEnd n gamma i ≤ n)
    (coordinate : Fin (gamma ^ i)) :
    contiguousSplit hfit
        (EpochGeometry.targetEmbedding n gamma i hfit coordinate) =
      Sum.inl coordinate := by
  unfold contiguousSplit
  rw [Equiv.trans_apply]
  rw [Equiv.sumCompl_symm_apply_of_pos
    (targetEmbedding_inTarget hfit coordinate)]
  simp only [Equiv.sumCongr_apply, Sum.map_inl]
  exact congrArg Sum.inl ((targetEquiv hfit).symm_apply_apply coordinate)

theorem contiguousSplit_eq_inr_of_not_target {n gamma i : ℕ}
    (hfit : EpochGeometry.epochEnd n gamma i ≤ n)
    (coordinate : Fin n) (houtside : ¬ InTarget n gamma i coordinate) :
    contiguousSplit hfit coordinate =
      Sum.inr (⟨coordinate, houtside⟩ : ContiguousOutside n gamma i) := by
  unfold contiguousSplit
  rw [Equiv.trans_apply]
  rw [Equiv.sumCompl_symm_apply_of_neg houtside]
  rfl


structure BlockContext (n gamma i : ℕ) where
  fit : EpochGeometry.epochEnd n gamma i ≤ n
  rows : RowMatrix n (HardSlice.rowCount n)
  outside : ContiguousOutside n gamma i → F2

namespace BlockContext

variable {n gamma i : ℕ}

def split (context : BlockContext n gamma i) :
    Fin n ≃ Sum (Fin (gamma ^ i)) (ContiguousOutside n gamma i) :=
  contiguousSplit context.fit

@[simp] theorem split_targetEmbedding (context : BlockContext n gamma i)
    (coordinate : Fin (gamma ^ i)) :
    context.split
        (EpochGeometry.targetEmbedding n gamma i context.fit coordinate) =
      Sum.inl coordinate :=
  contiguousSplit_targetEmbedding context.fit coordinate

def assembleInput (context : BlockContext n gamma i)
    (epoch : F2Vec (gamma ^ i)) : F2Vec n :=
  BlockAdapter.assembleInput context.split epoch context.outside

def booleanInput (context : BlockContext n gamma i)
    (epoch : F2Vec (gamma ^ i)) : BitVector n :=
  F2Bridge.boolVector (context.assembleInput epoch)

def referenceInput (context : BlockContext n gamma i) : BitVector n :=
  context.booleanInput (fun _ ↦ 0)

@[simp] theorem assembleInput_targetEmbedding
    (context : BlockContext n gamma i) (epoch : F2Vec (gamma ^ i))
    (coordinate : Fin (gamma ^ i)) :
    context.assembleInput epoch
        (EpochGeometry.targetEmbedding n gamma i context.fit coordinate) =
      epoch coordinate := by
  simp [assembleInput, BlockAdapter.assembleInput]

@[simp] theorem booleanInput_targetEmbedding
    (context : BlockContext n gamma i) (epoch : F2Vec (gamma ^ i))
    (coordinate : Fin (gamma ^ i)) :
    context.booleanInput epoch
        (EpochGeometry.targetEmbedding n gamma i context.fit coordinate) =
      F2Bridge.toBool (epoch coordinate) := by
  simp [booleanInput, F2Bridge.boolVector]

theorem assembleInput_eq_of_not_target
    (context : BlockContext n gamma i)
    (left right : F2Vec (gamma ^ i)) (coordinate : Fin n)
    (houtside : ¬ InTarget n gamma i coordinate) :
    context.assembleInput left coordinate =
      context.assembleInput right coordinate := by
  have hsplit := contiguousSplit_eq_inr_of_not_target
    context.fit coordinate houtside
  simp [assembleInput, split, BlockAdapter.assembleInput, hsplit]

theorem booleanInput_eq_of_not_target
    (context : BlockContext n gamma i)
    (left right : F2Vec (gamma ^ i)) (coordinate : Fin n)
    (houtside : ¬ InTarget n gamma i coordinate) :
    context.booleanInput left coordinate =
      context.booleanInput right coordinate := by
  exact congrArg F2Bridge.toBool
    (context.assembleInput_eq_of_not_target left right coordinate houtside)

def restrictedRows (context : BlockContext n gamma i) :
    RowMatrix (gamma ^ i) (HardSlice.rowCount n) :=
  BlockAdapter.epochRows context.split context.rows

noncomputable def fixedOutsideParity (context : BlockContext n gamma i) :
    Fin (HardSlice.rowCount n) → Bool :=
  BlockAdapter.outsideParity context.split context.rows context.outside

noncomputable def restrictedProblem (context : BlockContext n gamma i) :
    BinaryProblem (F2Vec (gamma ^ i)) (Fin (HardSlice.rowCount n)) :=
  InnerProductProblem.problem context.restrictedRows context.fixedOutsideParity

theorem restrictedProblem_value (context : BlockContext n gamma i)
    (query : Fin (HardSlice.rowCount n))
    (epoch : F2Vec (gamma ^ i)) :
    context.restrictedProblem.value query epoch =
      MultiphaseModel.innerProductAnswer
        (BlockAdapter.hardMatrix context.rows)
        (context.booleanInput epoch) query := by
  unfold restrictedProblem restrictedRows fixedOutsideParity
  unfold MultiphaseModel.innerProductAnswer booleanInput assembleInput
  exact BlockAdapter.problem_value_eq_hardSlice_innerProduct
    context.split context.rows context.outside query epoch

end BlockContext


def programsOn {n wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (input : BitVector n) (coordinates : List (Fin n)) :
    List (SCAToCellProbe.UpdateProgram wordBits Unit
      updateReads updateWrites) :=
  coordinates.map fun coordinate ↦
    dataStructure.update coordinate (input coordinate)

def allUpdatePrograms {n wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (input : BitVector n) :
    List (SCAToCellProbe.UpdateProgram wordBits Unit
      updateReads updateWrites) :=
  programsOn dataStructure input (List.finRange n)

@[simp] theorem allUpdatePrograms_length
    {n wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (input : BitVector n) :
    (allUpdatePrograms dataStructure input).length = n := by
  simp [allUpdatePrograms, programsOn]

theorem executeBatch_programsOn_memory
    {n wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (input : BitVector n) (memory : SCAToCellProbe.FiniteMemory wordBits)
    (coordinates : List (Fin n)) :
    (Staticization.executeBatch memory
      (programsOn dataStructure input coordinates)).memory =
      MultiphaseModel.runUpdateList dataStructure.update memory
        (coordinates.map fun coordinate ↦ (coordinate, input coordinate)) := by
  induction coordinates generalizing memory with
  | nil => rfl
  | cons coordinate rest ih =>
      simp only [programsOn, List.map_cons, Staticization.executeBatch,
        MultiphaseModel.runUpdateList]
      exact ih
        ((dataStructure.update coordinate (input coordinate)).execute memory).memory

theorem executeBatch_allUpdatePrograms_memory
    {n wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (input : BitVector n) (memory : SCAToCellProbe.FiniteMemory wordBits) :
    (Staticization.executeBatch memory
      (allUpdatePrograms dataStructure input)).memory =
      MultiphaseModel.runAllUpdates dataStructure.update memory input := by
  unfold allUpdatePrograms MultiphaseModel.runAllUpdates
  rw [executeBatch_programsOn_memory]
  rw [List.ofFn_eq_map]

theorem executeBatch_append_memory
    {wordBits updateReads updateWrites : ℕ}
    (memory : SCAToCellProbe.FiniteMemory wordBits)
    (first later : List (SCAToCellProbe.UpdateProgram wordBits Unit
      updateReads updateWrites)) :
    (Staticization.executeBatch memory (first ++ later)).memory =
      (Staticization.executeBatch
        (Staticization.executeBatch memory first).memory later).memory := by
  induction first generalizing memory with
  | nil => rfl
  | cons program rest ih =>
      simp only [List.cons_append, Staticization.executeBatch]
      exact ih (program.execute memory).memory


def prefixCoordinates (n gamma i : ℕ) : List (Fin n) :=
  (List.finRange n).take (EpochGeometry.epochStart n gamma i)

def targetCoordinates (n gamma i : ℕ) : List (Fin n) :=
  ((List.finRange n).drop (EpochGeometry.epochStart n gamma i)).take
    (gamma ^ i)

def recentCoordinates (n gamma i : ℕ) : List (Fin n) :=
  (List.finRange n).drop (EpochGeometry.epochEnd n gamma i)

theorem coordinate_partition (n gamma i : ℕ) :
    prefixCoordinates n gamma i ++ targetCoordinates n gamma i ++
        recentCoordinates n gamma i =
      List.finRange n := by
  simp only [prefixCoordinates, targetCoordinates, recentCoordinates,
    EpochGeometry.epochEnd, List.append_assoc,
    List.drop_take_append_drop, List.take_append_drop]

def prefixPrograms
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (context : BlockContext n gamma i) :
    List (SCAToCellProbe.UpdateProgram wordBits Unit
      updateReads updateWrites) :=
  programsOn dataStructure context.referenceInput (prefixCoordinates n gamma i)

def targetPrograms
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (context : BlockContext n gamma i) (epoch : F2Vec (gamma ^ i)) :
    List (SCAToCellProbe.UpdateProgram wordBits Unit
      updateReads updateWrites) :=
  programsOn dataStructure (context.booleanInput epoch)
    (targetCoordinates n gamma i)

def recentPrograms
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (context : BlockContext n gamma i) :
    List (SCAToCellProbe.UpdateProgram wordBits Unit
      updateReads updateWrites) :=
  programsOn dataStructure context.referenceInput (recentCoordinates n gamma i)

theorem targetPrograms_length
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (context : BlockContext n gamma i) (epoch : F2Vec (gamma ^ i)) :
    (targetPrograms dataStructure context epoch).length = gamma ^ i := by
  unfold targetPrograms programsOn targetCoordinates
  rw [List.length_map, List.length_take, List.length_drop,
    List.length_finRange]
  have hfit := context.fit
  rw [EpochGeometry.epochEnd] at hfit
  have htarget : gamma ^ i ≤ n - EpochGeometry.epochStart n gamma i := by
    omega
  exact min_eq_left htarget

theorem recentPrograms_length
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (context : BlockContext n gamma i) :
    (recentPrograms dataStructure context).length =
      n - EpochGeometry.epochEnd n gamma i := by
  simp [recentPrograms, programsOn, recentCoordinates]

theorem prefixPrograms_eq_variable
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (context : BlockContext n gamma i) (epoch : F2Vec (gamma ^ i)) :
    prefixPrograms dataStructure context =
      programsOn dataStructure (context.booleanInput epoch)
        (prefixCoordinates n gamma i) := by
  unfold prefixPrograms programsOn BlockContext.referenceInput
  apply List.map_congr_left
  intro coordinate hcoordinate
  apply congrArg (dataStructure.update coordinate)
  apply context.booleanInput_eq_of_not_target
  intro htarget
  have hlt : coordinate.val < EpochGeometry.epochStart n gamma i := by
    have hindex :=
      (List.mem_take_iff_idxOf_lt (List.mem_finRange coordinate)).mp hcoordinate
    simpa using hindex
  exact (Nat.not_le_of_gt hlt) htarget.1

theorem recentPrograms_eq_variable
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (context : BlockContext n gamma i) (epoch : F2Vec (gamma ^ i)) :
    recentPrograms dataStructure context =
      programsOn dataStructure (context.booleanInput epoch)
        (recentCoordinates n gamma i) := by
  unfold recentPrograms programsOn BlockContext.referenceInput
  apply List.map_congr_left
  intro coordinate hcoordinate
  apply congrArg (dataStructure.update coordinate)
  apply context.booleanInput_eq_of_not_target
  intro htarget
  have hend : EpochGeometry.epochEnd n gamma i ≤ coordinate.val := by
    by_contra hnot
    have hlt : coordinate.val < EpochGeometry.epochEnd n gamma i := by
      omega
    have htake : coordinate ∈
        (List.finRange n).take (EpochGeometry.epochEnd n gamma i) := by
      apply (List.mem_take_iff_idxOf_lt
        (List.mem_finRange coordinate)).mpr
      simpa using hlt
    exact
      (List.disjoint_take_drop (List.nodup_finRange n)
        (le_refl (EpochGeometry.epochEnd n gamma i))) htake hcoordinate
  exact (Nat.not_lt_of_ge hend) htarget.2

theorem phasePrograms_concat
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (context : BlockContext n gamma i) (epoch : F2Vec (gamma ^ i)) :
    prefixPrograms dataStructure context ++
        targetPrograms dataStructure context epoch ++
        recentPrograms dataStructure context =
      allUpdatePrograms dataStructure (context.booleanInput epoch) := by
  rw [prefixPrograms_eq_variable dataStructure context epoch,
    recentPrograms_eq_variable dataStructure context epoch]
  unfold targetPrograms allUpdatePrograms programsOn
  simp only [← List.map_append]
  rw [coordinate_partition]


def phasedProgram
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (context : BlockContext n gamma i) :
    Staticization.PhasedProgram
      (F2Vec (gamma ^ i)) (Fin (HardSlice.rowCount n))
      wordBits updateReads updateWrites queryReads (gamma ^ i) where
  initialMemory := dataStructure.preprocess (BlockAdapter.hardMatrix context.rows)
  prehistory := prefixPrograms dataStructure context
  target := targetPrograms dataStructure context
  target_length := targetPrograms_length dataStructure context
  recent := recentPrograms dataStructure context
  queryProgram := dataStructure.query

@[simp] theorem phasedProgram_queryProgram
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (context : BlockContext n gamma i)
    (query : Fin (HardSlice.rowCount n)) :
    (phasedProgram dataStructure context).queryProgram query =
      dataStructure.query query :=
  rfl

theorem phasedProgram_recent_memory
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (context : BlockContext n gamma i) (epoch : F2Vec (gamma ^ i)) :
    ((phasedProgram dataStructure context).recentExecution epoch).memory =
      MultiphaseModel.runAllUpdates dataStructure.update
        (dataStructure.preprocess (BlockAdapter.hardMatrix context.rows))
        (context.booleanInput epoch) := by
  change
    (Staticization.executeBatch
      (Staticization.executeBatch
        (Staticization.executeBatch
          (dataStructure.preprocess (BlockAdapter.hardMatrix context.rows))
          (prefixPrograms dataStructure context)).memory
        (targetPrograms dataStructure context epoch)).memory
      (recentPrograms dataStructure context)).memory = _
  calc
    _ = (Staticization.executeBatch
        (dataStructure.preprocess (BlockAdapter.hardMatrix context.rows))
        (prefixPrograms dataStructure context ++
          targetPrograms dataStructure context epoch ++
          recentPrograms dataStructure context)).memory := by
      symm
      rw [executeBatch_append_memory, executeBatch_append_memory]
    _ = (Staticization.executeBatch
        (dataStructure.preprocess (BlockAdapter.hardMatrix context.rows))
        (allUpdatePrograms dataStructure (context.booleanInput epoch))).memory := by
      rw [phasePrograms_concat]
    _ = _ := executeBatch_allUpdatePrograms_memory dataStructure
      (context.booleanInput epoch)
      (dataStructure.preprocess (BlockAdapter.hardMatrix context.rows))

theorem phasedProgram_queryExecution_result
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (context : BlockContext n gamma i) (epoch : F2Vec (gamma ^ i))
    (query : Fin (HardSlice.rowCount n)) :
    ((phasedProgram dataStructure context).queryExecution epoch query).result =
      MultiphaseModel.innerProductAnswer
        (BlockAdapter.hardMatrix context.rows)
        (context.booleanInput epoch) query := by
  unfold Staticization.PhasedProgram.queryExecution
  change
    ((dataStructure.query query).execute
      ((phasedProgram dataStructure context).recentExecution epoch).memory).result = _
  rw [phasedProgram_recent_memory]
  exact dataStructure.correct (BlockAdapter.hardMatrix context.rows)
    (context.booleanInput epoch) query

theorem static_solves_restrictedProblem
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (context : BlockContext n gamma i) :
    CellProbe.StaticStructure.Solves
      (Staticization.toStaticStructure (phasedProgram dataStructure context))
      context.restrictedProblem := by
  apply Staticization.PhasedProgram.static_solves
  intro epoch query
  rw [phasedProgram_queryExecution_result]
  exact (context.restrictedProblem_value query epoch).symm


theorem updateProgram_memory_eq_of_zero_writes
    {wordBits reads : ℕ} {Output : Type}
    (memory : SCAToCellProbe.FiniteMemory wordBits)
    (program : SCAToCellProbe.UpdateProgram wordBits Output reads 0) :
    (program.execute memory).memory = memory := by
  rw [SCAToCellProbe.UpdateProgram.execute_memory_eq_replay]
  have hwrites : (program.execute memory).writes = [] := by
    apply List.length_eq_zero_iff.mp
    exact SCAToCellProbe.UpdateProgram.execute_writes_length memory program
  rw [hwrites]
  rfl

theorem runUpdateList_memory_eq_of_zero_writes
    {n wordBits updateReads : ℕ}
    (update : Fin n → Bool →
      SCAToCellProbe.UpdateProgram wordBits Unit updateReads 0)
    (memory : SCAToCellProbe.FiniteMemory wordBits)
    (invocations : List (Fin n × Bool)) :
    MultiphaseModel.runUpdateList update memory invocations = memory := by
  induction invocations generalizing memory with
  | nil => rfl
  | cons invocation rest ih =>
      rcases invocation with ⟨coordinate, bit⟩
      simp only [MultiphaseModel.runUpdateList]
      rw [updateProgram_memory_eq_of_zero_writes]
      exact ih memory

theorem runAllUpdates_memory_eq_of_zero_writes
    {n wordBits updateReads : ℕ}
    (update : Fin n → Bool →
      SCAToCellProbe.UpdateProgram wordBits Unit updateReads 0)
    (memory : SCAToCellProbe.FiniteMemory wordBits) (input : BitVector n) :
    MultiphaseModel.runAllUpdates update memory input = memory := by
  unfold MultiphaseModel.runAllUpdates
  exact runUpdateList_memory_eq_of_zero_writes update memory _

theorem executeBatch_memory_eq_of_zero_writes
    {wordBits updateReads : ℕ}
    (memory : SCAToCellProbe.FiniteMemory wordBits)
    (programs : List
      (SCAToCellProbe.UpdateProgram wordBits Unit updateReads 0)) :
    (Staticization.executeBatch memory programs).memory = memory := by
  induction programs generalizing memory with
  | nil => rfl
  | cons program rest ih =>
      simp only [Staticization.executeBatch]
      rw [updateProgram_memory_eq_of_zero_writes]
      exact ih memory

theorem updateWrites_pos
    {n wordBits updateReads updateWrites queryReads : ℕ}
    (hn : 2 ≤ n)
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads) :
    0 < updateWrites := by
  apply Nat.pos_of_ne_zero
  intro hzero
  subst updateWrites
  classical
  have hnpos : 0 < n := by omega
  let coordinate : Fin n := ⟨0, hnpos⟩
  have hrowCount : 0 < HardSlice.rowCount n := by
    change 0 < n ^ 2
    exact pow_pos hnpos _
  let query : Fin (HardSlice.rowCount n) := ⟨0, hrowCount⟩
  let zeroVector : F2Vec n := fun _ ↦ 0
  let basisVector : F2Vec n := fun index ↦
    if index = coordinate then 1 else 0
  let matrix : IPMatrix n := fun _ ↦ F2Bridge.boolVector basisVector
  let zeroInput : BitVector n := F2Bridge.boolVector zeroVector
  let basisInput : BitVector n := F2Bridge.boolVector basisVector
  have hzeroMemory :
      MultiphaseModel.runAllUpdates dataStructure.update
          (dataStructure.preprocess matrix) zeroInput =
        dataStructure.preprocess matrix :=
    runAllUpdates_memory_eq_of_zero_writes dataStructure.update
      (dataStructure.preprocess matrix) zeroInput
  have hbasisMemory :
      MultiphaseModel.runAllUpdates dataStructure.update
          (dataStructure.preprocess matrix) basisInput =
        dataStructure.preprocess matrix :=
    runAllUpdates_memory_eq_of_zero_writes dataStructure.update
      (dataStructure.preprocess matrix) basisInput
  have hzeroCorrect := dataStructure.correct matrix zeroInput query
  have hbasisCorrect := dataStructure.correct matrix basisInput query
  rw [hzeroMemory] at hzeroCorrect
  rw [hbasisMemory] at hbasisCorrect
  have hanswers :
      MultiphaseModel.innerProductAnswer matrix zeroInput query =
        MultiphaseModel.innerProductAnswer matrix basisInput query :=
    hzeroCorrect.symm.trans hbasisCorrect
  have hdotZero : RandomCoherence.dotHom basisVector zeroVector = 0 := by
    simp [RandomCoherence.dotHom, zeroVector]
  have hdotBasis : RandomCoherence.dotHom basisVector basisVector = 1 := by
    simp [RandomCoherence.dotHom, basisVector]
  have hinnerZero :
      HardSlice.vectorInnerProduct (matrix query) zeroInput = 0 := by
    change HardSlice.vectorInnerProduct
      (F2Bridge.boolVector basisVector)
      (F2Bridge.boolVector zeroVector) = 0
    rw [F2Bridge.boolVector_innerProduct]
    exact hdotZero
  have hinnerBasis :
      HardSlice.vectorInnerProduct (matrix query) basisInput = 1 := by
    change HardSlice.vectorInnerProduct
      (F2Bridge.boolVector basisVector)
      (F2Bridge.boolVector basisVector) = 1
    rw [F2Bridge.boolVector_innerProduct]
    exact hdotBasis
  have hanswerZero :
      MultiphaseModel.innerProductAnswer matrix zeroInput query = false := by
    simp [MultiphaseModel.innerProductAnswer, hinnerZero]
  have hanswerBasis :
      MultiphaseModel.innerProductAnswer matrix basisInput query = true := by
    simp [MultiphaseModel.innerProductAnswer, hinnerBasis]
  have hfalse : false = true :=
    hanswerZero.symm.trans (hanswers.trans hanswerBasis)
  cases hfalse

end PegSeparation.LowerBound.PhasedMultiphase
