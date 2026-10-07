import PegSeparation.CFLNotPEG.LowerBound.BlockwiseMatrix
import PegSeparation.CFLNotPEG.LowerBound.PhasedMultiphase
import PegSeparation.CFLNotPEG.LowerBound.ProtocolEndgame


namespace PegSeparation.LowerBound.BlockContextGood

open PegSeparation
open PegSeparation.Witness
open PegSeparation.LowerBound

noncomputable section

abbrev F2 := RandomCoherence.F2
abbrev F2Vec := RandomCoherence.F2Vec

def selectedContext {n gamma ell : ℕ}
    {hell : 1 ≤ ell} {hgamma : 2 ≤ gamma}
    {hpower : gamma ^ ell ≤ n}
    (good : BlockwiseMatrix.BlockwiseGoodMatrix n gamma ell
      hell hgamma hpower)
    (i : BlockwiseMatrix.MiddleIndex ell)
    (outside : PhasedMultiphase.ContiguousOutside n gamma (i : ℕ) → F2) :
    PhasedMultiphase.BlockContext n gamma (i : ℕ) where
  fit := EpochGeometry.epochStart_add_power_le_updates
    hell hgamma hpower i.property
  rows := good.globalF2
  outside := outside

private theorem split_symm_inl_eq_targetEmbedding
    {n gamma i : ℕ} (context : PhasedMultiphase.BlockContext n gamma i)
    (coordinate : Fin (gamma ^ i)) :
    context.split.symm (Sum.inl coordinate) =
      EpochGeometry.targetEmbedding n gamma i context.fit coordinate := by
  apply context.split.injective
  simp

@[simp] theorem selectedContext_restrictedRows
    {n gamma ell : ℕ}
    {hell : 1 ≤ ell} {hgamma : 2 ≤ gamma}
    {hpower : gamma ^ ell ≤ n}
    (good : BlockwiseMatrix.BlockwiseGoodMatrix n gamma ell
      hell hgamma hpower)
    (i : BlockwiseMatrix.MiddleIndex ell)
    (outside : PhasedMultiphase.ContiguousOutside n gamma (i : ℕ) → F2) :
    (selectedContext good i outside).restrictedRows = good.rows i := by
  classical
  funext query coordinate
  change good.globalF2 query
      ((selectedContext good i outside).split.symm (Sum.inl coordinate)) =
    good.rows i query coordinate
  rw [split_symm_inl_eq_targetEmbedding]
  simpa [selectedContext, BlockwiseMatrix.middleTargetEmbedding] using
    good.restriction i query coordinate

theorem selectedContext_restrictedRows_ne_zero
    {n gamma ell : ℕ}
    {hell : 1 ≤ ell} {hgamma : 2 ≤ gamma}
    {hpower : gamma ^ ell ≤ n}
    (good : BlockwiseMatrix.BlockwiseGoodMatrix n gamma ell
      hell hgamma hpower)
    (i : BlockwiseMatrix.MiddleIndex ell)
    (outside : PhasedMultiphase.ContiguousOutside n gamma (i : ℕ) → F2)
    (query : Fin (HardSlice.rowCount n)) :
    (selectedContext good i outside).restrictedRows query ≠ 0 := by
  rw [selectedContext_restrictedRows]
  exact good.rows_nonzero i query

theorem selectedContext_kernel_le_four_sqrt
    {n gamma ell : ℕ}
    {hell : 1 ≤ ell} {hgamma : 2 ≤ gamma}
    {hpower : gamma ^ ell ≤ n}
    (good : BlockwiseMatrix.BlockwiseGoodMatrix n gamma ell
      hell hgamma hpower)
    (i : BlockwiseMatrix.MiddleIndex ell)
    (outside : PhasedMultiphase.ContiguousOutside n gamma (i : ℕ) → F2)
    (u : F2Vec (gamma ^ (i : ℕ))) (hu : u ≠ 0) :
    |RandomCoherence.kernel
        (selectedContext good i outside).restrictedRows u| ≤
      4 * Real.sqrt (((gamma ^ (i : ℕ) : ℕ) : ℝ) /
        HardSlice.rowCount n) := by
  rw [selectedContext_restrictedRows]
  exact good.kernel_le_four_sqrt i u hu

theorem selectedContext_restrictedProblem_isBalanced
    {n gamma ell : ℕ}
    {hell : 1 ≤ ell} {hgamma : 2 ≤ gamma}
    {hpower : gamma ^ ell ≤ n}
    (good : BlockwiseMatrix.BlockwiseGoodMatrix n gamma ell
      hell hgamma hpower)
    (i : BlockwiseMatrix.MiddleIndex ell)
    (outside : PhasedMultiphase.ContiguousOutside n gamma (i : ℕ) → F2) :
    (selectedContext good i outside).restrictedProblem.IsBalanced
      (ProtocolBridge.uniformFiniteDistribution
        (F2Vec (gamma ^ (i : ℕ)))) := by
  unfold PhasedMultiphase.BlockContext.restrictedProblem
  apply InnerProductProblem.problem_isBalanced
  exact selectedContext_restrictedRows_ne_zero good i outside

theorem selectedContext_protocolAdvantage_upper_fourthRoot
    {n gamma ell messageBits coinCount : ℕ}
    [Nonempty (Fin (HardSlice.rowCount n))]
    {hell : 1 ≤ ell} {hgamma : 2 ≤ gamma}
    {hpower : gamma ^ ell ≤ n}
    (good : BlockwiseMatrix.BlockwiseGoodMatrix n gamma ell
      hell hgamma hpower)
    (i : BlockwiseMatrix.MiddleIndex ell)
    (outside : PhasedMultiphase.ContiguousOutside n gamma (i : ℕ) → F2)
    (protocol : PublicCoinProtocol (F2Vec (gamma ^ (i : ℕ)))
      messageBits coinCount)
    (hn : 0 < n)
    (hmessage : (messageBits : ℝ) ≤
      ((gamma ^ (i : ℕ) : ℕ) : ℝ) / 2) :
    protocol.advantage (selectedContext good i outside).restrictedProblem
        (ProtocolBridge.uniformFiniteDistribution
          (F2Vec (gamma ^ (i : ℕ))))
        (ProtocolBridge.uniformFiniteDistribution (Fin (HardSlice.rowCount n))) ≤
      (2 : ℝ) ^ (-((gamma ^ (i : ℕ) : ℕ) : ℝ) / 4) +
        2 * (((gamma ^ (i : ℕ) : ℕ) : ℝ) /
          HardSlice.rowCount n) ^ (1 / 4 : ℝ) := by
  have hM : 0 < HardSlice.rowCount n := by
    simpa [HardSlice.rowCount] using pow_pos hn 2
  letI : Nonempty (Fin (HardSlice.rowCount n)) := ⟨⟨0, hM⟩⟩
  exact ProtocolEndgame.protocolAdvantage_upper_fourthRoot
    (selectedContext good i outside).restrictedRows
    (selectedContext good i outside).fixedOutsideParity protocol hM hmessage
    (selectedContext_kernel_le_four_sqrt good i outside)

theorem selectedContext_balanced_and_protocolAdvantage_upper_fourthRoot
    {n gamma ell messageBits coinCount : ℕ}
    [Nonempty (Fin (HardSlice.rowCount n))]
    {hell : 1 ≤ ell} {hgamma : 2 ≤ gamma}
    {hpower : gamma ^ ell ≤ n}
    (good : BlockwiseMatrix.BlockwiseGoodMatrix n gamma ell
      hell hgamma hpower)
    (i : BlockwiseMatrix.MiddleIndex ell)
    (outside : PhasedMultiphase.ContiguousOutside n gamma (i : ℕ) → F2)
    (protocol : PublicCoinProtocol (F2Vec (gamma ^ (i : ℕ)))
      messageBits coinCount)
    (hn : 0 < n)
    (hmessage : (messageBits : ℝ) ≤
      ((gamma ^ (i : ℕ) : ℕ) : ℝ) / 2) :
    (selectedContext good i outside).restrictedProblem.IsBalanced
        (ProtocolBridge.uniformFiniteDistribution
          (F2Vec (gamma ^ (i : ℕ)))) ∧
      protocol.advantage (selectedContext good i outside).restrictedProblem
          (ProtocolBridge.uniformFiniteDistribution
            (F2Vec (gamma ^ (i : ℕ))))
          (ProtocolBridge.uniformFiniteDistribution
            (Fin (HardSlice.rowCount n))) ≤
        (2 : ℝ) ^ (-((gamma ^ (i : ℕ) : ℕ) : ℝ) / 4) +
          2 * (((gamma ^ (i : ℕ) : ℕ) : ℝ) /
            HardSlice.rowCount n) ^ (1 / 4 : ℝ) := by
  have hM : 0 < HardSlice.rowCount n := by
    simpa [HardSlice.rowCount] using pow_pos hn 2
  letI : Nonempty (Fin (HardSlice.rowCount n)) := ⟨⟨0, hM⟩⟩
  exact ⟨selectedContext_restrictedProblem_isBalanced good i outside,
    selectedContext_protocolAdvantage_upper_fourthRoot
      good i outside protocol hn hmessage⟩

end

end PegSeparation.LowerBound.BlockContextGood
