import PegSeparation.CFLNotPEG.LowerBound.EpochGeometry
import PegSeparation.CFLNotPEG.LowerBound.CoherenceFour
import PegSeparation.CFLNotPEG.LowerBound.BlockAdapter
import PegSeparation.CFLNotPEG.Witness.HardSlice


open scoped BigOperators

namespace PegSeparation.LowerBound.BlockwiseMatrix

open PegSeparation.Witness

noncomputable section

abbrev F2 := RandomCoherence.F2
abbrev F2Vec := RandomCoherence.F2Vec
abbrev RowMatrix := RandomCoherence.RowMatrix

abbrev MiddleIndex (ell : ℕ) :=
  {i : ℕ // i ∈ Chronogram.middleEpochs ell}

abbrev EpochRows (n gamma ell : ℕ) :=
  ∀ i : MiddleIndex ell,
    RowMatrix (gamma ^ (i : ℕ)) (HardSlice.rowCount n)

def middleTargetEmbedding {n gamma ell : ℕ}
    (hell : 1 ≤ ell) (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n) (i : MiddleIndex ell) :
    Fin (gamma ^ (i : ℕ)) ↪ Fin n :=
  EpochGeometry.targetEmbedding n gamma i
    (EpochGeometry.epochStart_add_power_le_updates
      hell hgamma hpower i.property)

def embedVector {d n : ℕ} (e : Fin d ↪ Fin n)
    (v : F2Vec d) : F2Vec n :=
  fun x ↦ ∑ k : Fin d, if e k = x then v k else 0

@[simp]
theorem embedVector_apply_embedding {d n : ℕ} (e : Fin d ↪ Fin n)
    (v : F2Vec d) (k : Fin d) :
    embedVector e v (e k) = v k := by
  classical
  simp only [embedVector]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    have hne : e j ≠ e k := fun h ↦ hj (e.injective h)
    simp [hne]
  · simp

theorem embedVector_apply_eq_zero_of_forall_ne {d n : ℕ}
    (e : Fin d ↪ Fin n) (v : F2Vec d) (x : Fin n)
    (h : ∀ k, e k ≠ x) :
    embedVector e v x = 0 := by
  classical
  simp [embedVector, h]

def assembleRows {n gamma ell : ℕ}
    (hell : 1 ≤ ell) (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n) (rows : EpochRows n gamma ell) :
    RowMatrix n (HardSlice.rowCount n) :=
  fun q x ↦
    ∑ i : MiddleIndex ell,
      embedVector (middleTargetEmbedding hell hgamma hpower i)
        (rows i q) x

def assembleHardMatrix {n gamma ell : ℕ}
    (hell : 1 ≤ ell) (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n) (rows : EpochRows n gamma ell) :
    HardSlice.Matrix n :=
  BlockAdapter.hardMatrix (assembleRows hell hgamma hpower rows)

private theorem other_epoch_contribution_eq_zero {n gamma ell : ℕ}
    (hell : 1 ≤ ell) (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n) (rows : EpochRows n gamma ell)
    {i j : MiddleIndex ell} (hji : j ≠ i)
    (q : Fin (HardSlice.rowCount n)) (k : Fin (gamma ^ (i : ℕ))) :
    embedVector (middleTargetEmbedding hell hgamma hpower j)
        (rows j q) (middleTargetEmbedding hell hgamma hpower i k) = 0 := by
  apply embedVector_apply_eq_zero_of_forall_ne
  intro l hEq
  have hval : (j : ℕ) ≠ (i : ℕ) := by
    intro h
    apply hji
    exact Subtype.ext h
  have hdisjoint := EpochGeometry.targetImages_disjoint_of_ne
    hell hgamma hpower j.property i.property hval
  have hjmem :
      (middleTargetEmbedding hell hgamma hpower j l).val ∈
        EpochGeometry.targetImage n gamma (j : ℕ)
          (EpochGeometry.epochStart_add_power_le_updates
            hell hgamma hpower j.property) := by
    unfold EpochGeometry.targetImage
    refine Finset.mem_image.mpr ⟨l, Finset.mem_univ _, ?_⟩
    rfl
  have himem :
      (middleTargetEmbedding hell hgamma hpower i k).val ∈
        EpochGeometry.targetImage n gamma (i : ℕ)
          (EpochGeometry.epochStart_add_power_le_updates
            hell hgamma hpower i.property) := by
    unfold EpochGeometry.targetImage
    refine Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩
    rfl
  have hvals := congrArg Fin.val hEq
  rw [hvals] at hjmem
  exact (Finset.disjoint_left.mp hdisjoint) hjmem himem

@[simp]
theorem assembleRows_apply_middle {n gamma ell : ℕ}
    (hell : 1 ≤ ell) (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n) (rows : EpochRows n gamma ell)
    (i : MiddleIndex ell) (q : Fin (HardSlice.rowCount n))
    (k : Fin (gamma ^ (i : ℕ))) :
    assembleRows hell hgamma hpower rows q
        (middleTargetEmbedding hell hgamma hpower i k) = rows i q k := by
  classical
  simp only [assembleRows]
  rw [Finset.sum_eq_single i]
  · exact embedVector_apply_embedding
      (middleTargetEmbedding hell hgamma hpower i) (rows i q) k
  · intro j _ hji
    exact other_epoch_contribution_eq_zero
      hell hgamma hpower rows hji q k
  · simp

@[simp]
theorem assembleHardMatrix_apply_middle {n gamma ell : ℕ}
    (hell : 1 ≤ ell) (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n) (rows : EpochRows n gamma ell)
    (i : MiddleIndex ell) (q : Fin (HardSlice.rowCount n))
    (k : Fin (gamma ^ (i : ℕ))) :
    assembleHardMatrix hell hgamma hpower rows q
        (middleTargetEmbedding hell hgamma hpower i k) =
      F2Bridge.toBool (rows i q k) := by
  simp [assembleHardMatrix, BlockAdapter.hardMatrix, F2Bridge.boolVector]

structure BlockwiseGoodMatrix (n gamma ell : ℕ)
    (hell : 1 ≤ ell) (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n) where
  rows : EpochRows n gamma ell
  globalF2 : RowMatrix n (HardSlice.rowCount n)
  global : HardSlice.Matrix n
  globalF2_eq_assemble :
    globalF2 = assembleRows hell hgamma hpower rows
  global_eq_booleanization :
    global = BlockAdapter.hardMatrix globalF2
  restriction : ∀ (i : MiddleIndex ell)
      (q : Fin (HardSlice.rowCount n)) (k : Fin (gamma ^ (i : ℕ))),
    globalF2 q (middleTargetEmbedding hell hgamma hpower i k) = rows i q k
  boolean_restriction : ∀ (i : MiddleIndex ell)
      (q : Fin (HardSlice.rowCount n)) (k : Fin (gamma ^ (i : ℕ))),
    global q (middleTargetEmbedding hell hgamma hpower i k) =
      F2Bridge.toBool (rows i q k)
  rows_nonzero : ∀ (i : MiddleIndex ell) (q : Fin (HardSlice.rowCount n)),
    rows i q ≠ 0
  kernel_le_four_sqrt : ∀ (i : MiddleIndex ell)
      (u : F2Vec (gamma ^ (i : ℕ))), u ≠ 0 →
    |RandomCoherence.kernel (rows i) u| ≤
      4 * Real.sqrt (((gamma ^ (i : ℕ) : ℕ) : ℝ) /
        HardSlice.rowCount n)

theorem exists_blockwiseGoodMatrix {n gamma ell : ℕ}
    (hn : 0 < n) (hell : 1 ≤ ell) (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n)
    (hd : ∀ i : MiddleIndex ell, 2 ≤ gamma ^ (i : ℕ))
    (hzero : ∀ i : MiddleIndex ell,
      (HardSlice.rowCount n : ℝ) /
          (2 : ℝ) ^ (gamma ^ (i : ℕ)) < 1 / 8) :
    Nonempty (BlockwiseGoodMatrix n gamma ell hell hgamma hpower) := by
  classical
  have hM : 0 < HardSlice.rowCount n := by
    change 0 < n ^ 2
    exact pow_pos hn _
  have hExists : ∀ i : MiddleIndex ell,
      ∃ S : RowMatrix (gamma ^ (i : ℕ)) (HardSlice.rowCount n),
        (∀ q, S q ≠ 0) ∧
          (∀ u : F2Vec (gamma ^ (i : ℕ)), u ≠ 0 →
            |RandomCoherence.kernel S u| ≤
              4 * Real.sqrt (((gamma ^ (i : ℕ) : ℕ) : ℝ) /
                HardSlice.rowCount n)) := by
    intro i
    exact RandomCoherence.exists_matrix_no_zero_row_kernel_le_four_sqrt
      (gamma ^ (i : ℕ)) (HardSlice.rowCount n) (hd i) hM (hzero i)
  choose chosen hchosen using hExists
  let globalF2 : RowMatrix n (HardSlice.rowCount n) :=
    assembleRows hell hgamma hpower chosen
  let global : HardSlice.Matrix n := BlockAdapter.hardMatrix globalF2
  refine ⟨{
    rows := chosen
    globalF2 := globalF2
    global := global
    globalF2_eq_assemble := rfl
    global_eq_booleanization := rfl
    restriction := ?_
    boolean_restriction := ?_
    rows_nonzero := ?_
    kernel_le_four_sqrt := ?_
  }⟩
  · intro i q k
    exact assembleRows_apply_middle hell hgamma hpower chosen i q k
  · intro i q k
    exact assembleHardMatrix_apply_middle hell hgamma hpower chosen i q k
  · intro i q
    exact (hchosen i).1 q
  · intro i u hu
    exact (hchosen i).2 u hu

end

end PegSeparation.LowerBound.BlockwiseMatrix
