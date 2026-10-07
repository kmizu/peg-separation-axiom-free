import PegSeparation.CFLNotPEG.LowerBound.Staticization


namespace PegSeparation.LowerBound.Staticization

open PegSeparation.CellProbe
open PegSeparation.Reduction


@[simp] theorem writtenAddresses_append {wordBits : ℕ}
    (first later : List (SCAToCellProbe.WriteEntry wordBits)) :
    writtenAddresses (first ++ later) =
      writtenAddresses first ∪ writtenAddresses later := by
  ext address
  simp [writtenAddresses]

theorem executeBatch_append {wordBits reads writes : ℕ}
    (initial : SCAToCellProbe.FiniteMemory wordBits)
    (first later :
      List (SCAToCellProbe.UpdateProgram wordBits Unit reads writes)) :
    executeBatch initial (first ++ later) =
      { memory :=
          (executeBatch (executeBatch initial first).memory later).memory
        readTrace :=
          (executeBatch initial first).readTrace ++
            (executeBatch (executeBatch initial first).memory later).readTrace
        writes :=
          (executeBatch initial first).writes ++
            (executeBatch (executeBatch initial first).memory later).writes } := by
  induction first generalizing initial with
  | nil =>
      simp only [List.nil_append, executeBatch]
  | cons program rest ih =>
      simp only [List.cons_append, executeBatch]
      rw [ih]
      simp only [List.append_assoc]

theorem executeBatch_append_memory {wordBits reads writes : ℕ}
    (initial : SCAToCellProbe.FiniteMemory wordBits)
    (first later :
      List (SCAToCellProbe.UpdateProgram wordBits Unit reads writes)) :
    (executeBatch initial (first ++ later)).memory =
      (executeBatch (executeBatch initial first).memory later).memory := by
  rw [executeBatch_append]

theorem executeBatch_append_readTrace {wordBits reads writes : ℕ}
    (initial : SCAToCellProbe.FiniteMemory wordBits)
    (first later :
      List (SCAToCellProbe.UpdateProgram wordBits Unit reads writes)) :
    (executeBatch initial (first ++ later)).readTrace =
      (executeBatch initial first).readTrace ++
        (executeBatch (executeBatch initial first).memory later).readTrace := by
  rw [executeBatch_append]

theorem executeBatch_append_writes {wordBits reads writes : ℕ}
    (initial : SCAToCellProbe.FiniteMemory wordBits)
    (first later :
      List (SCAToCellProbe.UpdateProgram wordBits Unit reads writes)) :
    (executeBatch initial (first ++ later)).writes =
      (executeBatch initial first).writes ++
        (executeBatch (executeBatch initial first).memory later).writes := by
  rw [executeBatch_append]


theorem targetWriterProbeCount_eq_epochOccurrences_card
    {Epoch : Type} [DecidableEq Epoch] {wordBits : ℕ}
    (queryTrace : List (Address wordBits))
    (newer older : List Epoch) (target : Epoch)
    (epochWrites : Epoch → List (SCAToCellProbe.WriteEntry wordBits))
    (targetWrites recentWrites :
      List (SCAToCellProbe.WriteEntry wordBits))
    (horder : (newer ++ target :: older).Nodup)
    (htarget : writtenAddresses targetWrites =
      writtenAddresses (epochWrites target))
    (hrecent : writtenAddresses recentWrites =
      writtenByEpochs newer epochWrites) :
    targetWriterProbeCount queryTrace targetWrites recentWrites =
      (Chronogram.epochOccurrences
        (probeOccurrences queryTrace)
        (occurrenceLastWriter (newer ++ target :: older)
          epochWrites queryTrace)
        target).card := by
  classical
  unfold targetWriterProbeCount Chronogram.epochOccurrences probeOccurrences
  rw [← Nat.count_eq_card_filter_range]
  unfold Nat.count
  rw [← List.map_get_finRange queryTrace]
  simp only [List.countP_map]
  simp only [List.map_get_finRange]
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.countP_map]
  apply List.countP_congr
  intro index _
  simp only [Function.comp_apply]
  have hoccurrence : (index : ℕ) ∈ probeOccurrences queryTrace := by
    simp [probeOccurrences, index.isLt]
  rw [occurrenceLastWriter_of_mem
    (newer ++ target :: older) epochWrites queryTrace index hoccurrence]
  simp only [decide_eq_true_eq]
  rw [newestWriter_split_iff_staticLastWriter_target
    newer older target epochWrites horder]
  simp only [htarget, hrecent]

end PegSeparation.LowerBound.Staticization
