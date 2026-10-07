import PegSeparation.CFLNotPEG.LowerBound.PhasedMultiphase
import PegSeparation.CFLNotPEG.LowerBound.StaticizationExtensions


namespace PegSeparation.LowerBound.EpochTraceBridge

open PegSeparation
open PegSeparation.Witness
open PegSeparation.Reduction
open PegSeparation.CellProbe

abbrev F2 := RandomCoherence.F2
abbrev F2Vec := RandomCoherence.F2Vec
abbrev RowMatrix := RandomCoherence.RowMatrix
abbrev BitVector := MultiphaseModel.BitVector


def geometricEpochOrder (ell : ℕ) : List ℕ :=
  List.Ico 1 ell

@[simp] theorem mem_geometricEpochOrder {ell j : ℕ} :
    j ∈ geometricEpochOrder ell ↔ j ∈ Finset.Ico 1 ell := by
  simp [geometricEpochOrder]

theorem geometricEpochOrder_nodup (ell : ℕ) :
    (geometricEpochOrder ell).Nodup :=
  List.Ico.nodup 1 ell

def newerEpochs (i : ℕ) : List ℕ :=
  List.Ico 1 i

def olderEpochs (i ell : ℕ) : List ℕ :=
  List.Ico (i + 1) ell

@[simp] theorem mem_newerEpochs {i j : ℕ} :
    j ∈ newerEpochs i ↔ j ∈ Finset.Ico 1 i := by
  simp [newerEpochs]

@[simp] theorem mem_olderEpochs {i ell j : ℕ} :
    j ∈ olderEpochs i ell ↔ j ∈ Finset.Ico (i + 1) ell := by
  simp [olderEpochs]

theorem geometricEpochOrder_split {ell i : ℕ}
    (hi : i ∈ Finset.Ico 1 ell) :
    geometricEpochOrder ell =
      newerEpochs i ++ i :: olderEpochs i ell := by
  have honei : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  have hiell : i + 1 ≤ ell := by
    have := (Finset.mem_Ico.mp hi).2
    omega
  unfold geometricEpochOrder newerEpochs olderEpochs
  calc
    List.Ico 1 ell = List.Ico 1 i ++ List.Ico i ell :=
      (List.Ico.append_consecutive honei (Nat.le_of_lt
        (Finset.mem_Ico.mp hi).2)).symm
    _ = List.Ico 1 i ++ (List.Ico i (i + 1) ++
          List.Ico (i + 1) ell) := by
      rw [List.Ico.append_consecutive (Nat.le_succ i) hiell]
    _ = List.Ico 1 i ++ i :: List.Ico (i + 1) ell := by
      simp

theorem newerEpochs_succ {i : ℕ} (hi : 1 ≤ i) :
    newerEpochs (i + 1) = newerEpochs i ++ [i] := by
  exact List.Ico.succ_top hi


theorem peeledMass_succ_le_updates_of_mem
    {n gamma ell i : ℕ} (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n) (hi : i ∈ Finset.Ico 1 ell) :
    Chronogram.peeledMass gamma (i + 1) ≤ n := by
  have hisucc : i + 1 ≤ ell := by
    have := (Finset.mem_Ico.mp hi).2
    omega
  exact (Chronogram.peeledMass_mono gamma hisucc).trans
    ((Chronogram.peeledMass_lt_power hgamma).le.trans hpower)

theorem epochEnd_le_updates_of_mem
    {n gamma ell i : ℕ} (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n) (hi : i ∈ Finset.Ico 1 ell) :
    EpochGeometry.epochEnd n gamma i ≤ n := by
  have hione : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  rw [EpochGeometry.epochEnd_eq_sub_peeledMass hione
    (peeledMass_succ_le_updates_of_mem hgamma hpower hi)]
  exact Nat.sub_le _ _

def booleanFullInput {n : ℕ} (X : F2Vec n) : BitVector n :=
  F2Bridge.boolVector X

def globalUpdateExecution
    {n wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n) :
    Staticization.BatchExecution wordBits :=
  Staticization.executeBatch
    (dataStructure.preprocess (BlockAdapter.hardMatrix rows))
    (PhasedMultiphase.allUpdatePrograms dataStructure (booleanFullInput X))

def globalWriteTrace
    {n wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n) :
    List (SCAToCellProbe.WriteEntry wordBits) :=
  (globalUpdateExecution dataStructure rows X).writes

def globalQueryTrace
    {n wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (query : Fin (HardSlice.rowCount n)) :
    List (Address wordBits) :=
  ((dataStructure.query query).execute
    (globalUpdateExecution dataStructure rows X).memory).trace

def actualPrefixExecution
    {n wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (gamma j : ℕ) : Staticization.BatchExecution wordBits :=
  Staticization.executeBatch
    (dataStructure.preprocess (BlockAdapter.hardMatrix rows))
    (PhasedMultiphase.programsOn dataStructure (booleanFullInput X)
      (PhasedMultiphase.prefixCoordinates n gamma j))

def actualEpochExecution
    {n wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (gamma j : ℕ) : Staticization.BatchExecution wordBits :=
  Staticization.executeBatch
    (actualPrefixExecution dataStructure rows X gamma j).memory
    (PhasedMultiphase.programsOn dataStructure (booleanFullInput X)
      (PhasedMultiphase.targetCoordinates n gamma j))

def actualEpochWrites
    {n wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (gamma j : ℕ) : List (SCAToCellProbe.WriteEntry wordBits) :=
  (actualEpochExecution dataStructure rows X gamma j).writes

def actualRecentExecution
    {n wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (gamma j : ℕ) : Staticization.BatchExecution wordBits :=
  Staticization.executeBatch
    (actualEpochExecution dataStructure rows X gamma j).memory
    (PhasedMultiphase.programsOn dataStructure (booleanFullInput X)
      (PhasedMultiphase.recentCoordinates n gamma j))

def actualRecentWrites
    {n wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (gamma j : ℕ) : List (SCAToCellProbe.WriteEntry wordBits) :=
  (actualRecentExecution dataStructure rows X gamma j).writes


theorem actualPrograms_concat
    {n gamma j wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads) (X : F2Vec n) :
    PhasedMultiphase.programsOn dataStructure (booleanFullInput X)
          (PhasedMultiphase.prefixCoordinates n gamma j) ++
        PhasedMultiphase.programsOn dataStructure (booleanFullInput X)
          (PhasedMultiphase.targetCoordinates n gamma j) ++
        PhasedMultiphase.programsOn dataStructure (booleanFullInput X)
          (PhasedMultiphase.recentCoordinates n gamma j) =
      PhasedMultiphase.allUpdatePrograms dataStructure (booleanFullInput X) := by
  unfold PhasedMultiphase.programsOn PhasedMultiphase.allUpdatePrograms
  simp only [← List.map_append]
  rw [PhasedMultiphase.coordinate_partition]
  rfl

theorem globalWriteTrace_partition
    {n gamma j wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n) :
    globalWriteTrace dataStructure rows X =
      (actualPrefixExecution dataStructure rows X gamma j).writes ++
        actualEpochWrites dataStructure rows X gamma j ++
        actualRecentWrites dataStructure rows X gamma j := by
  unfold globalWriteTrace globalUpdateExecution actualPrefixExecution
    actualEpochWrites actualEpochExecution actualRecentWrites
    actualRecentExecution
  rw [← actualPrograms_concat (gamma := gamma) (j := j) dataStructure X]
  rw [Staticization.executeBatch_append_writes]
  rw [Staticization.executeBatch_append_writes]
  unfold actualPrefixExecution actualEpochExecution
  rw [Staticization.executeBatch_append_memory]
  rfl

@[simp] theorem globalWriteTrace_length
    {n wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n) :
    (globalWriteTrace dataStructure rows X).length = n * updateWrites := by
  unfold globalWriteTrace globalUpdateExecution
  rw [Staticization.executeBatch_writes_length]
  simp

theorem actualPrefixWrites_length
    {n gamma j wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (hfit : EpochGeometry.epochEnd n gamma j ≤ n) :
    (actualPrefixExecution dataStructure rows X gamma j).writes.length =
      EpochGeometry.epochStart n gamma j * updateWrites := by
  unfold actualPrefixExecution
  rw [Staticization.executeBatch_writes_length]
  unfold PhasedMultiphase.programsOn PhasedMultiphase.prefixCoordinates
  simp only [List.length_map, List.length_take, List.length_finRange]
  rw [min_eq_left]
  exact (Nat.le_add_right _ _).trans hfit

theorem actualEpochWrites_length
    {n gamma j wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (hfit : EpochGeometry.epochEnd n gamma j ≤ n) :
    (actualEpochWrites dataStructure rows X gamma j).length =
      gamma ^ j * updateWrites := by
  unfold actualEpochWrites actualEpochExecution
  rw [Staticization.executeBatch_writes_length]
  unfold PhasedMultiphase.programsOn PhasedMultiphase.targetCoordinates
  simp only [List.length_map, List.length_take, List.length_drop,
    List.length_finRange]
  have htarget : gamma ^ j ≤ n - EpochGeometry.epochStart n gamma j := by
    rw [EpochGeometry.epochEnd] at hfit
    omega
  rw [min_eq_left htarget]

theorem actualEpochWrites_eq_global_slice
    {n gamma j wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (hfit : EpochGeometry.epochEnd n gamma j ≤ n) :
    actualEpochWrites dataStructure rows X gamma j =
      ((globalWriteTrace dataStructure rows X).drop
        (EpochGeometry.epochStart n gamma j * updateWrites)).take
          (gamma ^ j * updateWrites) := by
  rw [globalWriteTrace_partition (gamma := gamma) (j := j)]
  rw [← actualPrefixWrites_length dataStructure rows X hfit]
  rw [← actualEpochWrites_length dataStructure rows X hfit]
  simp

theorem actualRecentWrites_eq_global_drop
    {n gamma j wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (hfit : EpochGeometry.epochEnd n gamma j ≤ n) :
    actualRecentWrites dataStructure rows X gamma j =
      (globalWriteTrace dataStructure rows X).drop
        (EpochGeometry.epochEnd n gamma j * updateWrites) := by
  rw [globalWriteTrace_partition (gamma := gamma) (j := j)]
  simp only [EpochGeometry.epochEnd, Nat.add_mul]
  rw [← actualPrefixWrites_length dataStructure rows X hfit]
  rw [← actualEpochWrites_length dataStructure rows X hfit]
  simp

theorem epochStart_eq_epochEnd_succ
    {n gamma i : ℕ} (hi : 1 ≤ i)
    (hfit : Chronogram.peeledMass gamma (i + 2) ≤ n) :
    EpochGeometry.epochStart n gamma i =
      EpochGeometry.epochEnd n gamma (i + 1) := by
  rw [EpochGeometry.epochEnd_eq_sub_peeledMass (by omega)]
  · rfl
  · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfit

theorem actualRecentWrites_succ
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (hi : 1 ≤ i)
    (hfit : Chronogram.peeledMass gamma (i + 2) ≤ n) :
    actualRecentWrites dataStructure rows X gamma (i + 1) =
      actualEpochWrites dataStructure rows X gamma i ++
        actualRecentWrites dataStructure rows X gamma i := by
  have hfitCurrent : EpochGeometry.epochEnd n gamma i ≤ n := by
    rw [EpochGeometry.epochEnd_eq_sub_peeledMass hi]
    · exact Nat.sub_le _ _
    · exact (Chronogram.peeledMass_mono gamma (by omega)).trans hfit
  have hfitSucc : EpochGeometry.epochEnd n gamma (i + 1) ≤ n := by
    rw [EpochGeometry.epochEnd_eq_sub_peeledMass (by omega)]
    · exact Nat.sub_le _ _
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfit
  rw [actualRecentWrites_eq_global_drop dataStructure rows X hfitSucc]
  rw [actualEpochWrites_eq_global_slice dataStructure rows X hfitCurrent]
  rw [actualRecentWrites_eq_global_drop dataStructure rows X hfitCurrent]
  rw [← epochStart_eq_epochEnd_succ hi hfit]
  simp [EpochGeometry.epochEnd, Nat.add_mul]

theorem writtenByEpochs_append
    {Epoch : Type} {wordBits : ℕ}
    (first later : List Epoch)
    (writes : Epoch → List (SCAToCellProbe.WriteEntry wordBits)) :
    Staticization.writtenByEpochs (first ++ later) writes =
      Staticization.writtenByEpochs first writes ∪
        Staticization.writtenByEpochs later writes := by
  classical
  induction first with
  | nil => simp
  | cons epoch rest ih =>
      simp only [List.cons_append, Staticization.writtenByEpochs_cons, ih]
      ext address
      simp

theorem actualRecentWrittenAddresses_eq_writtenByEpochs
    {n wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (gamma i : ℕ) (hi : 1 ≤ i)
    (hfit : Chronogram.peeledMass gamma (i + 1) ≤ n) :
    Staticization.writtenAddresses
        (actualRecentWrites dataStructure rows X gamma i) =
      Staticization.writtenByEpochs (newerEpochs i)
        (actualEpochWrites dataStructure rows X gamma) := by
  induction i with
  | zero => omega
  | succ i ih =>
      by_cases hizero : i = 0
      · subst i
        have hend : EpochGeometry.epochEnd n gamma 1 = n := by
          rw [EpochGeometry.epochEnd_eq_sub_peeledMass (by omega) hfit]
          simp [Chronogram.peeledMass]
        have honefit : EpochGeometry.epochEnd n gamma 1 ≤ n := by
          rw [hend]
        rw [actualRecentWrites_eq_global_drop dataStructure rows X honefit]
        rw [hend]
        have hlength := globalWriteTrace_length dataStructure rows X
        rw [List.drop_eq_nil_of_le (by rw [hlength])]
        simp [newerEpochs, Staticization.writtenAddresses]
      · have hipos : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hizero
        have hfitPrev : Chronogram.peeledMass gamma (i + 1) ≤ n :=
          (Chronogram.peeledMass_mono gamma (by omega)).trans hfit
        have ih' := ih hipos hfitPrev
        rw [actualRecentWrites_succ dataStructure rows X hipos]
        · rw [Staticization.writtenAddresses_append, ih']
          rw [newerEpochs_succ hipos]
          rw [writtenByEpochs_append]
          simp only [Staticization.writtenByEpochs_cons,
            Staticization.writtenByEpochs_nil, Finset.union_empty]
          exact Finset.union_comm _ _
        · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfit


def selectedBlockContext
    {n gamma i : ℕ} (hfit : EpochGeometry.epochEnd n gamma i ≤ n)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n) :
    PhasedMultiphase.BlockContext n gamma i where
  fit := hfit
  rows := rows
  outside := BlockAdapter.outsideInput
    (PhasedMultiphase.contiguousSplit hfit) X

def selectedEpochInput
    {n gamma i : ℕ} (hfit : EpochGeometry.epochEnd n gamma i ≤ n)
    (X : F2Vec n) : F2Vec (gamma ^ i) :=
  BlockAdapter.epochInput (PhasedMultiphase.contiguousSplit hfit) X

@[simp] theorem selectedBlockContext_assembleInput
    {n gamma i : ℕ} (hfit : EpochGeometry.epochEnd n gamma i ≤ n)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n) :
    (selectedBlockContext hfit rows X).assembleInput
        (selectedEpochInput hfit X) = X := by
  exact BlockAdapter.assembleInput_epochInput_outsideInput
    (PhasedMultiphase.contiguousSplit hfit) X

@[simp] theorem selectedBlockContext_booleanInput
    {n gamma i : ℕ} (hfit : EpochGeometry.epochEnd n gamma i ≤ n)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n) :
    (selectedBlockContext hfit rows X).booleanInput
        (selectedEpochInput hfit X) = booleanFullInput X := by
  unfold PhasedMultiphase.BlockContext.booleanInput booleanFullInput
  rw [selectedBlockContext_assembleInput]

theorem selected_targetExecution_eq_actualEpochExecution
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (hfit : EpochGeometry.epochEnd n gamma i ≤ n) :
    (PhasedMultiphase.phasedProgram dataStructure
        (selectedBlockContext hfit rows X)).targetExecution
          (selectedEpochInput hfit X) =
      actualEpochExecution dataStructure rows X gamma i := by
  change
    Staticization.executeBatch
        (Staticization.executeBatch
          (dataStructure.preprocess (BlockAdapter.hardMatrix rows))
          (PhasedMultiphase.prefixPrograms dataStructure
            (selectedBlockContext hfit rows X))).memory
        (PhasedMultiphase.targetPrograms dataStructure
          (selectedBlockContext hfit rows X) (selectedEpochInput hfit X)) =
      Staticization.executeBatch
        (Staticization.executeBatch
          (dataStructure.preprocess (BlockAdapter.hardMatrix rows))
          (PhasedMultiphase.programsOn dataStructure (booleanFullInput X)
            (PhasedMultiphase.prefixCoordinates n gamma i))).memory
        (PhasedMultiphase.programsOn dataStructure (booleanFullInput X)
          (PhasedMultiphase.targetCoordinates n gamma i))
  rw [PhasedMultiphase.prefixPrograms_eq_variable dataStructure
    (selectedBlockContext hfit rows X) (selectedEpochInput hfit X)]
  unfold PhasedMultiphase.targetPrograms
  rw [selectedBlockContext_booleanInput]

theorem selected_target_writtenAddresses_eq_actual
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (hfit : EpochGeometry.epochEnd n gamma i ≤ n) :
    Staticization.writtenAddresses
        ((PhasedMultiphase.phasedProgram dataStructure
          (selectedBlockContext hfit rows X)).targetExecution
            (selectedEpochInput hfit X)).writes =
      Staticization.writtenAddresses
        (actualEpochWrites dataStructure rows X gamma i) := by
  rw [selected_targetExecution_eq_actualEpochExecution]
  rfl

theorem selected_recentExecution_eq_actualRecentExecution
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (hfit : EpochGeometry.epochEnd n gamma i ≤ n) :
    (PhasedMultiphase.phasedProgram dataStructure
        (selectedBlockContext hfit rows X)).recentExecution
          (selectedEpochInput hfit X) =
      actualRecentExecution dataStructure rows X gamma i := by
  unfold Staticization.PhasedProgram.recentExecution actualRecentExecution
  rw [selected_targetExecution_eq_actualEpochExecution]
  unfold PhasedMultiphase.phasedProgram
  rw [PhasedMultiphase.recentPrograms_eq_variable dataStructure
    (selectedBlockContext hfit rows X) (selectedEpochInput hfit X)]
  rw [selectedBlockContext_booleanInput]

theorem selected_recent_writtenAddresses_eq_actualEpochs
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (hfit : EpochGeometry.epochEnd n gamma i ≤ n)
    (hi : 1 ≤ i)
    (hmass : Chronogram.peeledMass gamma (i + 1) ≤ n) :
    Staticization.writtenAddresses
        ((PhasedMultiphase.phasedProgram dataStructure
          (selectedBlockContext hfit rows X)).recentExecution
            (selectedEpochInput hfit X)).writes =
      Staticization.writtenByEpochs (newerEpochs i)
        (actualEpochWrites dataStructure rows X gamma) := by
  rw [selected_recentExecution_eq_actualRecentExecution]
  exact actualRecentWrittenAddresses_eq_writtenByEpochs
    dataStructure rows X gamma i hi hmass

theorem selected_phased_queryTrace_eq_globalQueryTrace
    {n gamma i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (hfit : EpochGeometry.epochEnd n gamma i ≤ n)
    (query : Fin (HardSlice.rowCount n)) :
    ((PhasedMultiphase.phasedProgram dataStructure
      (selectedBlockContext hfit rows X)).queryExecution
        (selectedEpochInput hfit X) query).trace =
      globalQueryTrace dataStructure rows X query := by
  change
    ((dataStructure.query query).execute
      ((PhasedMultiphase.phasedProgram dataStructure
        (selectedBlockContext hfit rows X)).recentExecution
          (selectedEpochInput hfit X)).memory).trace =
      ((dataStructure.query query).execute
        (globalUpdateExecution dataStructure rows X).memory).trace
  rw [PhasedMultiphase.phasedProgram_recent_memory]
  unfold globalUpdateExecution
  rw [PhasedMultiphase.executeBatch_allUpdatePrograms_memory]
  rw [selectedBlockContext_booleanInput]
  rfl


theorem selected_targetWriterProbeCount_eq_epochOccurrences_card
    {n gamma ell i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) (X : F2Vec n)
    (query : Fin (HardSlice.rowCount n))
    (hgamma : 2 ≤ gamma) (hpower : gamma ^ ell ≤ n)
    (hi : i ∈ Finset.Ico 1 ell) :
    let hfit := epochEnd_le_updates_of_mem hgamma hpower hi
    Staticization.targetWriterProbeCount
        (globalQueryTrace dataStructure rows X query)
        ((PhasedMultiphase.phasedProgram dataStructure
          (selectedBlockContext hfit rows X)).targetExecution
            (selectedEpochInput hfit X)).writes
        ((PhasedMultiphase.phasedProgram dataStructure
          (selectedBlockContext hfit rows X)).recentExecution
            (selectedEpochInput hfit X)).writes =
      (Chronogram.epochOccurrences
        (Staticization.probeOccurrences
          (globalQueryTrace dataStructure rows X query))
        (Staticization.occurrenceLastWriter (geometricEpochOrder ell)
          (actualEpochWrites dataStructure rows X gamma)
          (globalQueryTrace dataStructure rows X query)) i).card := by
  dsimp only
  let hfit : EpochGeometry.epochEnd n gamma i ≤ n :=
    epochEnd_le_updates_of_mem hgamma hpower hi
  have hsplit := geometricEpochOrder_split hi
  have horder :
      (newerEpochs i ++ i :: olderEpochs i ell).Nodup := by
    rw [← hsplit]
    exact geometricEpochOrder_nodup ell
  have htarget := selected_target_writtenAddresses_eq_actual
    dataStructure rows X hfit
  have hrecent := selected_recent_writtenAddresses_eq_actualEpochs
    dataStructure rows X hfit (Finset.mem_Ico.mp hi).1
      (peeledMass_succ_le_updates_of_mem hgamma hpower hi)
  have hidentity :=
    Staticization.targetWriterProbeCount_eq_epochOccurrences_card
      (globalQueryTrace dataStructure rows X query)
      (newerEpochs i) (olderEpochs i ell) i
      (actualEpochWrites dataStructure rows X gamma)
      ((PhasedMultiphase.phasedProgram dataStructure
        (selectedBlockContext hfit rows X)).targetExecution
          (selectedEpochInput hfit X)).writes
      ((PhasedMultiphase.phasedProgram dataStructure
        (selectedBlockContext hfit rows X)).recentExecution
          (selectedEpochInput hfit X)).writes
      horder htarget hrecent
  rw [← hsplit] at hidentity
  exact hidentity

end PegSeparation.LowerBound.EpochTraceBridge
