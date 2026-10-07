import PegSeparation.CFLNotPEG.LowerBound.EpochTraceBridge
import PegSeparation.CFLNotPEG.LowerBound.FiniteAveraging


open scoped BigOperators

namespace PegSeparation.LowerBound.EpochSelection

open PegSeparation
open PegSeparation.Witness
open PegSeparation.Reduction
open PegSeparation.CellProbe

noncomputable section

abbrev F2 := RandomCoherence.F2
abbrev F2Vec := RandomCoherence.F2Vec
abbrev RowMatrix := RandomCoherence.RowMatrix


def contextOfOutside {n gamma i : ℕ}
    (hfit : EpochGeometry.epochEnd n gamma i ≤ n)
    (rows : RowMatrix n (HardSlice.rowCount n))
    (outside : PhasedMultiphase.ContiguousOutside n gamma i → F2) :
    PhasedMultiphase.BlockContext n gamma i where
  fit := hfit
  rows := rows
  outside := outside

@[simp] theorem contextOfOutside_assembleInput
    {n gamma i : ℕ}
    (hfit : EpochGeometry.epochEnd n gamma i ≤ n)
    (rows : RowMatrix n (HardSlice.rowCount n))
    (outside : PhasedMultiphase.ContiguousOutside n gamma i → F2)
    (epoch : F2Vec (gamma ^ i)) :
    (contextOfOutside hfit rows outside).assembleInput epoch =
      BlockAdapter.assembleInput (PhasedMultiphase.contiguousSplit hfit)
        epoch outside :=
  rfl

@[simp] theorem selectedBlockContext_assembled_eq_contextOfOutside
    {n gamma i : ℕ}
    (hfit : EpochGeometry.epochEnd n gamma i ≤ n)
    (rows : RowMatrix n (HardSlice.rowCount n))
    (outside : PhasedMultiphase.ContiguousOutside n gamma i → F2)
    (epoch : F2Vec (gamma ^ i)) :
    EpochTraceBridge.selectedBlockContext hfit rows
        (BlockAdapter.assembleInput
          (PhasedMultiphase.contiguousSplit hfit) epoch outside) =
      contextOfOutside hfit rows outside := by
  unfold EpochTraceBridge.selectedBlockContext contextOfOutside
  rw [BlockAdapter.outsideInput_assembleInput]

@[simp] theorem selectedEpochInput_assembled
    {n gamma i : ℕ}
    (hfit : EpochGeometry.epochEnd n gamma i ≤ n)
    (epoch : F2Vec (gamma ^ i))
    (outside : PhasedMultiphase.ContiguousOutside n gamma i → F2) :
    EpochTraceBridge.selectedEpochInput hfit
        (BlockAdapter.assembleInput
          (PhasedMultiphase.contiguousSplit hfit) epoch outside) =
      epoch := by
  exact BlockAdapter.epochInput_assembleInput
    (PhasedMultiphase.contiguousSplit hfit) epoch outside


theorem fixedOutside_targetWriterProbeCount_eq_epochOccurrences_card
    {n gamma ell i wordBits updateReads updateWrites queryReads : ℕ}
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n))
    (hgamma : 2 ≤ gamma) (hpower : gamma ^ ell ≤ n)
    (hi : i ∈ Finset.Ico 1 ell)
    (outside : PhasedMultiphase.ContiguousOutside n gamma i → F2)
    (epoch : F2Vec (gamma ^ i))
    (query : Fin (HardSlice.rowCount n)) :
    let hfit := EpochTraceBridge.epochEnd_le_updates_of_mem
      hgamma hpower hi
    let context := contextOfOutside hfit rows outside
    let program := PhasedMultiphase.phasedProgram dataStructure context
    Staticization.targetWriterProbeCount
        (program.queryExecution epoch query).trace
        (program.targetExecution epoch).writes
        (program.recentExecution epoch).writes =
      (Chronogram.epochOccurrences
        (Staticization.probeOccurrences
          (EpochTraceBridge.globalQueryTrace dataStructure rows
            (BlockAdapter.assembleInput
              (PhasedMultiphase.contiguousSplit hfit) epoch outside) query))
        (Staticization.occurrenceLastWriter
          (EpochTraceBridge.geometricEpochOrder ell)
          (EpochTraceBridge.actualEpochWrites dataStructure rows
            (BlockAdapter.assembleInput
              (PhasedMultiphase.contiguousSplit hfit) epoch outside) gamma)
          (EpochTraceBridge.globalQueryTrace dataStructure rows
            (BlockAdapter.assembleInput
              (PhasedMultiphase.contiguousSplit hfit) epoch outside) query)) i).card := by
  dsimp only
  let hfit : EpochGeometry.epochEnd n gamma i ≤ n :=
    EpochTraceBridge.epochEnd_le_updates_of_mem hgamma hpower hi
  let full : F2Vec n :=
    BlockAdapter.assembleInput (PhasedMultiphase.contiguousSplit hfit)
      epoch outside
  let context : PhasedMultiphase.BlockContext n gamma i :=
    contextOfOutside hfit rows outside
  let program := PhasedMultiphase.phasedProgram dataStructure context
  have hcontext :
      EpochTraceBridge.selectedBlockContext hfit rows full = context := by
    simp [full, context]
  have hepoch :
      EpochTraceBridge.selectedEpochInput hfit full = epoch := by
    simp [full]
  have hquery :=
    EpochTraceBridge.selected_phased_queryTrace_eq_globalQueryTrace
      dataStructure rows full hfit query
  rw [hcontext, hepoch] at hquery
  have hcharge :=
    EpochTraceBridge.selected_targetWriterProbeCount_eq_epochOccurrences_card
      dataStructure rows full query hgamma hpower hi
  dsimp only at hcharge
  rw [hcontext, hepoch] at hcharge
  change
    Staticization.targetWriterProbeCount
        (program.queryExecution epoch query).trace
        (program.targetExecution epoch).writes
        (program.recentExecution epoch).writes = _
  rw [hquery]
  simpa [full, hfit] using hcharge


theorem exists_middle_epoch_outside_small_numerator
    {n ell gamma wordBits updateReads updateWrites queryReads : ℕ}
    (hell : 2 ≤ ell) (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n)
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) :
    ∃ (i : ℕ) (hi : i ∈ Chronogram.middleEpochs ell)
      (outside : PhasedMultiphase.ContiguousOutside n gamma i → F2),
      let hiIco := EpochGeometry.middleEpoch_mem_Ico (by omega) hi
      let hfit := EpochTraceBridge.epochEnd_le_updates_of_mem
        hgamma hpower hiIco
      let context := contextOfOutside hfit rows outside
      let program := PhasedMultiphase.phasedProgram dataStructure context
      (∑ epoch : F2Vec (gamma ^ i),
          ∑ query : Fin (HardSlice.rowCount n),
            Staticization.targetWriterProbeCount
              (program.queryExecution epoch query).trace
              (program.targetExecution epoch).writes
              (program.recentExecution epoch).writes) *
          (Chronogram.middleEpochs ell).card ≤
        Fintype.card (F2Vec (gamma ^ i)) *
          HardSlice.rowCount n * queryReads := by
  classical
  have hellOne : 1 ≤ ell := by omega
  have hgammaPos : 0 < gamma := by omega
  have hn : 0 < n :=
    (Nat.pow_pos hgammaPos).trans_le hpower
  have hqueries : 0 < HardSlice.rowCount n := by
    simpa [HardSlice.rowCount] using Nat.pow_pos hn (n := 2)
  letI : Nonempty (Fin (HardSlice.rowCount n)) :=
    ⟨⟨0, hqueries⟩⟩
  obtain ⟨i, hi, hcheap⟩ :=
    Staticization.exists_cheap_actual_epoch_on_average
      (samples := (Finset.univ :
        Finset (F2Vec n × Fin (HardSlice.rowCount n))))
      (queryTrace := fun sample ↦
        EpochTraceBridge.globalQueryTrace dataStructure rows
          sample.1 sample.2)
      (newestFirst := EpochTraceBridge.geometricEpochOrder ell)
      (epochWrites := fun sample epoch ↦
        EpochTraceBridge.actualEpochWrites dataStructure rows sample.1
          gamma epoch)
      (epochs := Chronogram.middleEpochs ell)
      (Chronogram.middleEpochs_nonempty hell)
  have hiIco : i ∈ Finset.Ico 1 ell :=
    EpochGeometry.middleEpoch_mem_Ico hellOne hi
  let hfit : EpochGeometry.epochEnd n gamma i ≤ n :=
    EpochTraceBridge.epochEnd_le_updates_of_mem hgamma hpower hiIco
  let split : Fin n ≃ Sum (Fin (gamma ^ i))
      (PhasedMultiphase.ContiguousOutside n gamma i) :=
    PhasedMultiphase.contiguousSplit hfit
  let globalCharge : F2Vec n → Fin (HardSlice.rowCount n) → ℕ :=
    fun full query ↦
      (Chronogram.epochOccurrences
        (Staticization.probeOccurrences
          (EpochTraceBridge.globalQueryTrace dataStructure rows full query))
        (Staticization.occurrenceLastWriter
          (EpochTraceBridge.geometricEpochOrder ell)
          (EpochTraceBridge.actualEpochWrites dataStructure rows full gamma)
          (EpochTraceBridge.globalQueryTrace dataStructure rows full query)) i).card
  let localCharge : F2Vec (gamma ^ i) →
      (PhasedMultiphase.ContiguousOutside n gamma i → F2) →
      Fin (HardSlice.rowCount n) → ℕ :=
    fun epoch outside query ↦
      let context := contextOfOutside hfit rows outside
      let program := PhasedMultiphase.phasedProgram dataStructure context
      Staticization.targetWriterProbeCount
        (program.queryExecution epoch query).trace
        (program.targetExecution epoch).writes
        (program.recentExecution epoch).writes
  have htraceLength (full : F2Vec n)
      (query : Fin (HardSlice.rowCount n)) :
      (EpochTraceBridge.globalQueryTrace dataStructure rows full query).length =
        queryReads := by
    unfold EpochTraceBridge.globalQueryTrace
    exact SCAToCellProbe.ReadProgram.execute_trace_length _ _
  change
    (∑ sample : F2Vec n × Fin (HardSlice.rowCount n),
        globalCharge sample.1 sample.2) *
          (Chronogram.middleEpochs ell).card ≤
      ∑ sample : F2Vec n × Fin (HardSlice.rowCount n),
        (EpochTraceBridge.globalQueryTrace dataStructure rows
          sample.1 sample.2).length at hcheap
  rw [Fintype.sum_prod_type] at hcheap
  simp_rw [htraceLength] at hcheap
  have hglobal :
      (∑ full : F2Vec n,
          ∑ query : Fin (HardSlice.rowCount n), globalCharge full query) *
          (Chronogram.middleEpochs ell).card ≤
        Fintype.card (F2Vec n) * HardSlice.rowCount n * queryReads := by
    simpa [globalCharge, Nat.mul_assoc] using hcheap
  have hreindex :
      (∑ full : F2Vec n,
          ∑ query : Fin (HardSlice.rowCount n), globalCharge full query) =
        ∑ epoch : F2Vec (gamma ^ i),
          ∑ outside : PhasedMultiphase.ContiguousOutside n gamma i → F2,
            ∑ query : Fin (HardSlice.rowCount n),
              localCharge epoch outside query := by
    rw [BlockAdapter.sum_full_eq_sum_epoch_outside split
      (fun full ↦ ∑ query : Fin (HardSlice.rowCount n),
        globalCharge full query)]
    apply Finset.sum_congr rfl
    intro epoch _
    apply Finset.sum_congr rfl
    intro outside _
    apply Finset.sum_congr rfl
    intro query _
    symm
    simpa [split, globalCharge, localCharge, hfit] using
              fixedOutside_targetWriterProbeCount_eq_epochOccurrences_card
        dataStructure rows hgamma hpower hiIco outside epoch query
  rw [hreindex] at hglobal
  have hcardSplit :
      Fintype.card (F2Vec n) =
        Fintype.card (F2Vec (gamma ^ i)) *
          Fintype.card
            (PhasedMultiphase.ContiguousOutside n gamma i → F2) := by
    calc
      Fintype.card (F2Vec n) =
          Fintype.card
            (F2Vec (gamma ^ i) ×
              (PhasedMultiphase.ContiguousOutside n gamma i → F2)) :=
        Fintype.card_congr (BlockAdapter.inputSplitEquiv split).symm
      _ = _ := Fintype.card_prod _ _
  have hglobalForContext :
      (∑ epoch : F2Vec (gamma ^ i),
          ∑ outside : PhasedMultiphase.ContiguousOutside n gamma i → F2,
            ∑ query : Fin (HardSlice.rowCount n),
              localCharge epoch outside query) *
          (Chronogram.middleEpochs ell).card ≤
        Fintype.card (F2Vec (gamma ^ i)) *
          Fintype.card
            (PhasedMultiphase.ContiguousOutside n gamma i → F2) *
          Fintype.card (Fin (HardSlice.rowCount n)) * queryReads := by
    rw [hcardSplit] at hglobal
    simpa [Nat.mul_assoc] using hglobal
  obtain ⟨outside, houtside⟩ :=
    FiniteAveraging.exists_context_of_total_mul_le
      (A := F2Vec (gamma ^ i))
      (B := PhasedMultiphase.ContiguousOutside n gamma i → F2)
      (Q := Fin (HardSlice.rowCount n))
      localCharge (Chronogram.middleEpochs ell).card queryReads
        hglobalForContext
  refine ⟨i, hi, outside, ?_⟩
  simpa [localCharge, hfit, hiIco] using houtside


theorem exists_middle_epoch_outside_expectedUpdatedProbes_le
    {n ell gamma wordBits updateReads updateWrites queryReads : ℕ}
    [Nonempty (Fin (HardSlice.rowCount n))]
    (hell : 2 ≤ ell) (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n)
    (dataStructure : MultiphaseModel.ExactMultiphaseIP n wordBits
      updateReads updateWrites queryReads)
    (rows : RowMatrix n (HardSlice.rowCount n)) :
    ∃ (i : ℕ) (hi : i ∈ Chronogram.middleEpochs ell)
      (outside : PhasedMultiphase.ContiguousOutside n gamma i → F2),
      let hiIco := EpochGeometry.middleEpoch_mem_Ico (by omega) hi
      let hfit := EpochTraceBridge.epochEnd_le_updates_of_mem
        hgamma hpower hiIco
      let context := contextOfOutside hfit rows outside
      let program := PhasedMultiphase.phasedProgram dataStructure context
      (Staticization.toStaticStructure program).expectedUpdatedProbes
          (ProtocolBridge.uniformFiniteDistribution (F2Vec (gamma ^ i)))
          (ProtocolBridge.uniformFiniteDistribution
            (Fin (HardSlice.rowCount n))) ≤
        (queryReads : ℝ) / (Chronogram.middleEpochs ell).card := by
  classical
  obtain ⟨i, hi, outside, hcleared⟩ :=
    exists_middle_epoch_outside_small_numerator hell hgamma hpower
      dataStructure rows
  have hiIco : i ∈ Finset.Ico 1 ell :=
    EpochGeometry.middleEpoch_mem_Ico (by omega) hi
  let hfit : EpochGeometry.epochEnd n gamma i ≤ n :=
    EpochTraceBridge.epochEnd_le_updates_of_mem hgamma hpower hiIco
  let context : PhasedMultiphase.BlockContext n gamma i :=
    contextOfOutside hfit rows outside
  let program := PhasedMultiphase.phasedProgram dataStructure context
  let localCharge : F2Vec (gamma ^ i) →
      Fin (HardSlice.rowCount n) → ℕ :=
    fun epoch query ↦
      Staticization.targetWriterProbeCount
        (program.queryExecution epoch query).trace
        (program.targetExecution epoch).writes
        (program.recentExecution epoch).writes
  have hcard : 0 < (Chronogram.middleEpochs ell).card :=
    Finset.card_pos.mpr (Chronogram.middleEpochs_nonempty hell)
  have hcleared' :
      (∑ epoch : F2Vec (gamma ^ i),
          ∑ query : Fin (HardSlice.rowCount n), localCharge epoch query) *
          (Chronogram.middleEpochs ell).card ≤
        Fintype.card (F2Vec (gamma ^ i)) *
          Fintype.card (Fin (HardSlice.rowCount n)) * queryReads := by
    simpa [localCharge, program, context, hfit, hiIco] using hcleared
  have hnormalized :=
    FiniteAveraging.uniformNatExpectation_le_div_of_total_mul_le
      localCharge (Chronogram.middleEpochs ell).card queryReads hcard hcleared'
  refine ⟨i, hi, outside, ?_⟩
  change
    (Staticization.toStaticStructure program).expectedUpdatedProbes
        (ProtocolBridge.uniformFiniteDistribution (F2Vec (gamma ^ i)))
        (ProtocolBridge.uniformFiniteDistribution
          (Fin (HardSlice.rowCount n))) ≤
      (queryReads : ℝ) / (Chronogram.middleEpochs ell).card
  calc
    (Staticization.toStaticStructure program).expectedUpdatedProbes
        (ProtocolBridge.uniformFiniteDistribution (F2Vec (gamma ^ i)))
        (ProtocolBridge.uniformFiniteDistribution
          (Fin (HardSlice.rowCount n))) =
        FiniteAveraging.uniformNatExpectation localCharge := by
      rw [program.expectedUpdatedProbes_eq_targetWriterProbeCount]
      rfl
    _ ≤ (queryReads : ℝ) / (Chronogram.middleEpochs ell).card :=
      hnormalized

end

end PegSeparation.LowerBound.EpochSelection
