import PegSeparation.CFLNotPEG.External.LarsenYuUpperBounds
import PegSeparation.CFLNotPEG.LowerBound.FamilyScale
import PegSeparation.CFLNotPEG.LowerBound.EpochSelection
import PegSeparation.CFLNotPEG.LowerBound.BlockContextGood


namespace PegSeparation.LowerBound.MultiphaseLowerBound

open PegSeparation
open PegSeparation.Witness
open PegSeparation.Reduction
open PegSeparation.CellProbe

noncomputable section

theorem not_hasFastMultiphaseIPFamily
    (external : InternalLowerBoundAssumptions) :
    ¬ MultiphaseModel.HasFastMultiphaseIPFamily := by
  rintro ⟨wordScale, queryScale, updateReads, updateWrites,
    hwordScale, hqueryScale, family⟩
  obtain ⟨smallStructure⟩ := family 2 (by omega)
  have hupdateWrites : 0 < updateWrites :=
    PhasedMultiphase.updateWrites_pos (by omega) smallStructure
  obtain ⟨A, a, hA, ha, larsenYu⟩ :=
    external.larsenYuBetaOne_upperBounds
  obtain ⟨R, _hRmin, certificate⟩ :=
    FamilyScale.exists_scaleCertificate wordScale queryScale updateWrites
      A a hA ha hupdateWrites 6
  have hRone : 1 ≤ R := by omega
  have hRtwo : 2 ≤ R := by omega
  have hnTwo : 2 ≤ LargeScale.updateCount R := by
    have hlog : 1 ≤ LargeScale.logScale R := by
      unfold LargeScale.logScale
      exact Nat.one_le_pow 16 R hRone
    unfold LargeScale.updateCount
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ LargeScale.logScale R :=
        Nat.pow_le_pow_right (by norm_num) hlog
  have hnPos : 0 < LargeScale.updateCount R := by omega
  have hellTwo : 2 ≤ LargeScale.epochCount R :=
    LargeScale.epochCount_ge_two hRtwo
  have hellOne : 1 ≤ LargeScale.epochCount R := by omega
  have hgamma : 2 ≤ LargeScale.epochBase R :=
    LargeScale.epochBase_ge_two hRone
  have hpower :
      LargeScale.epochBase R ^ LargeScale.epochCount R ≤
        LargeScale.updateCount R :=
    certificate.geometry_power.le
  obtain ⟨dataStructure⟩ := family (LargeScale.updateCount R) hnTwo
  have hblockDimension
      (j : BlockwiseMatrix.MiddleIndex (LargeScale.epochCount R)) :
      2 ≤ LargeScale.epochBase R ^ (j : ℕ) := by
    simpa [LargeScale.epochDimension] using
      certificate.dimension_ge_two (j : ℕ) j.property
  have hzeroRowBudget
      (j : BlockwiseMatrix.MiddleIndex (LargeScale.epochCount R)) :
      (HardSlice.rowCount (LargeScale.updateCount R) : ℝ) /
          (2 : ℝ) ^ (LargeScale.epochBase R ^ (j : ℕ)) < 1 / 8 := by
    simpa [FamilyScale.collisionRatio, LargeScale.epochDimension,
      HardSlice.rowCount] using
        certificate.collision_lt_eighth (j : ℕ) j.property
  obtain ⟨good⟩ := BlockwiseMatrix.exists_blockwiseGoodMatrix
    hnPos hellOne hgamma hpower hblockDimension hzeroRowBudget
  have hqueryCount :
      0 < HardSlice.rowCount (LargeScale.updateCount R) := by
    change 0 < LargeScale.updateCount R ^ 2
    positivity
  letI : Nonempty
      (Fin (HardSlice.rowCount (LargeScale.updateCount R))) :=
    ⟨⟨0, hqueryCount⟩⟩
  obtain ⟨i, hi, outside, hselectedUpdated⟩ :=
    EpochSelection.exists_middle_epoch_outside_expectedUpdatedProbes_le
      hellTwo hgamma hpower dataStructure good.globalF2
  let middleIndex : BlockwiseMatrix.MiddleIndex
      (LargeScale.epochCount R) := ⟨i, hi⟩
  let hiIco : i ∈ Finset.Ico 1 (LargeScale.epochCount R) :=
    EpochGeometry.middleEpoch_mem_Ico hellOne hi
  let averageFit :
      EpochGeometry.epochEnd (LargeScale.updateCount R)
          (LargeScale.epochBase R) i ≤ LargeScale.updateCount R :=
    EpochTraceBridge.epochEnd_le_updates_of_mem hgamma hpower hiIco
  let averageContext := EpochSelection.contextOfOutside averageFit
    good.globalF2 outside
  let context := BlockContextGood.selectedContext good middleIndex outside
  have averageContext_eq : averageContext = context := by
    unfold averageContext context EpochSelection.contextOfOutside
      BlockContextGood.selectedContext
    rfl
  let program := PhasedMultiphase.phasedProgram dataStructure context
  let staticStructure := Staticization.toStaticStructure program
  let inputDistribution :=
    ProtocolBridge.uniformFiniteDistribution
      (PhasedMultiphase.F2Vec (LargeScale.epochBase R ^ i))
  let queryDistribution :=
    ProtocolBridge.uniformFiniteDistribution
      (Fin (HardSlice.rowCount (LargeScale.updateCount R)))
  have hselectedUpdated' :
      staticStructure.expectedUpdatedProbes inputDistribution
          queryDistribution ≤
        (FamilyScale.familyQueryReads queryScale R : ℝ) /
          (Chronogram.middleEpochs (LargeScale.epochCount R)).card := by
    change
      (Staticization.toStaticStructure
          (PhasedMultiphase.phasedProgram dataStructure averageContext)).expectedUpdatedProbes
              (ProtocolBridge.uniformFiniteDistribution
                (PhasedMultiphase.F2Vec
                  (LargeScale.epochBase R ^ i)))
              (ProtocolBridge.uniformFiniteDistribution
                (Fin (HardSlice.rowCount (LargeScale.updateCount R)))) ≤
        (FamilyScale.familyQueryReads queryScale R : ℝ) /
          (Chronogram.middleEpochs (LargeScale.epochCount R)).card at hselectedUpdated
    rw [averageContext_eq] at hselectedUpdated
    simpa [staticStructure, program, inputDistribution,
      queryDistribution] using hselectedUpdated
  have hbalanced :
      context.restrictedProblem.IsBalanced inputDistribution := by
    simpa [context, inputDistribution] using
      BlockContextGood.selectedContext_restrictedProblem_isBalanced
        good middleIndex outside
  have hsolves :
      CellProbe.StaticStructure.Solves staticStructure
        context.restrictedProblem := by
    simpa [staticStructure, program] using
      PhasedMultiphase.static_solves_restrictedProblem
        dataStructure context
  have htotal :
      staticStructure.expectedTotalProbes inputDistribution
          queryDistribution ≤
        (FamilyScale.familyQueryReads queryScale R : ℝ) := by
    simpa [staticStructure, program, inputDistribution, queryDistribution,
      FamilyScale.familyQueryReads] using
      (Staticization.PhasedProgram.expectedTotalProbes_le program
        inputDistribution queryDistribution)
  have hupdated :
      staticStructure.expectedUpdatedProbes inputDistribution
          queryDistribution ≤
        (FamilyScale.updatedConstant queryScale : ℝ) * (R : ℝ) :=
    hselectedUpdated'.trans certificate.query_per_middle_epoch
  have hwordBits : 0 < FamilyScale.familyWordBits wordScale R := by
    unfold FamilyScale.familyWordBits MultiphaseModel.scaledLogBudget
      MultiphaseModel.logScale
    exact Nat.mul_pos hwordScale (by omega)
  obtain ⟨messageBits, coinCount, protocol, hmessage, hlowerRaw⟩ :=
    larsenYu context.restrictedProblem inputDistribution queryDistribution
      staticStructure
      (FamilyScale.familyQueryReads queryScale R : ℝ)
      ((FamilyScale.updatedConstant queryScale : ℝ) * (R : ℝ))
      (LargeScale.sampleProbability R)
      hwordBits hbalanced hsolves htotal hupdated
      certificate.sample_pos certificate.sample_le_half
  have hiOne : 1 ≤ i :=
    (Finset.mem_Ico.mp
      (EpochGeometry.middleEpoch_mem_Ico hellOne hi)).1
  have hmassFit :
      Chronogram.peeledMass (LargeScale.epochBase R) (i + 1) ≤
        LargeScale.updateCount R :=
    EpochGeometry.peeledMass_succ_le_updates hellOne hgamma hpower hi
  have hmass :
      Chronogram.peeledMass (LargeScale.epochBase R) i ≤
        LargeScale.updateCount R :=
    (Chronogram.peeledMass_mono (LargeScale.epochBase R)
      (by omega : i ≤ i + 1)).trans hmassFit
  have hrecent :
      program.recent.length =
        Chronogram.peeledMass (LargeScale.epochBase R) i := by
    change
      (PhasedMultiphase.recentPrograms dataStructure context).length = _
    rw [PhasedMultiphase.recentPrograms_length]
    rw [EpochGeometry.epochEnd_eq_sub_peeledMass hiOne hmassFit]
    omega
  change
    (messageBits : ℝ) ≤
      (8 * LargeScale.sampleProbability R *
            (((LargeScale.epochBase R ^ i) * updateWrites : ℕ) : ℝ) +
          (((program.recent.length * updateWrites) +
              (program.recent.length * updateWrites) : ℕ) : ℝ)) *
          (FamilyScale.familyWordBits wordScale R : ℝ) + 2 at hmessage
  have hmessageCap :
      (messageBits : ℝ) ≤
        (LargeScale.epochDimension R i : ℝ) / 2 := by
    calc
      (messageBits : ℝ) ≤
          (8 * LargeScale.sampleProbability R *
                (((LargeScale.epochBase R ^ i) * updateWrites : ℕ) : ℝ) +
              (((program.recent.length * updateWrites) +
                  (program.recent.length * updateWrites) : ℕ) : ℝ)) *
              (FamilyScale.familyWordBits wordScale R : ℝ) + 2 := hmessage
      _ = FamilyScale.familyMessageCost wordScale updateWrites R i := by
        rw [hrecent]
        unfold FamilyScale.familyMessageCost LargeScale.epochDimension
        push_cast
        ring
      _ ≤ (LargeScale.epochDimension R i : ℝ) / 2 :=
        certificate.message_cap i hi
  have hadvantageUpper :=
    BlockContextGood.selectedContext_protocolAdvantage_upper_fourthRoot
      good middleIndex outside protocol hnPos hmessageCap
  have hadvantageUpper' :
      protocol.advantage context.restrictedProblem inputDistribution
          queryDistribution ≤
        (2 : ℝ) ^ (-((LargeScale.epochDimension R i : ℝ) / 4)) +
          2 * ((LargeScale.epochDimension R i : ℝ) /
            (LargeScale.updateCount R : ℝ) ^ 2) ^ (1 / 4 : ℝ) := by
    simpa [context, inputDistribution, queryDistribution,
      LargeScale.epochDimension, HardSlice.rowCount, middleIndex,
      neg_div] using hadvantageUpper
  have hlower :
      Parameters.mainTerm
          (FamilyScale.familyExponent A queryScale R) -
          Parameters.overflowTerm a (LargeScale.sampleProbability R)
            (((updateWrites * LargeScale.epochDimension R i : ℕ) : ℝ)) ≤
        protocol.advantage context.restrictedProblem inputDistribution
          queryDistribution := by
    simpa only [Real.rpow_eq_pow, Parameters.mainTerm,
      Parameters.overflowTerm,
      FamilyScale.familyExponent, Parameters.correctedExponent,
      FamilyScale.familyLambda, LargeScale.logInvSample,
      LargeScale.epochDimension, middleIndex, Nat.mul_comm, neg_mul,
      mul_assoc] using
        hlowerRaw
  have hnReal : (1 : ℝ) ≤ (LargeScale.updateCount R : ℝ) := by
    exact_mod_cast (show 1 ≤ LargeScale.updateCount R by omega)
  have hdNonnegative :
      0 ≤ (LargeScale.epochDimension R i : ℝ) := by positivity
  have hdLower :
      (LargeScale.logScale R : ℝ) ≤
        (LargeScale.epochDimension R i : ℝ) := by
    exact_mod_cast certificate.dimension_ge_log i hi
  have hthreshold :
      2 * (1 + (2 : ℝ)) <
        (2 : ℝ) ^ ((LargeScale.logScale R : ℝ) / 8) := by
    norm_num
    exact certificate.separation_threshold
  exact Parameters.no_advantage_between_dimension_bounds
    (adv := protocol.advantage context.restrictedProblem inputDistribution
      queryDistribution)
    (exponent := FamilyScale.familyExponent A queryScale R)
    (a := a)
    (p := LargeScale.sampleProbability R)
    (S := ((updateWrites * LargeScale.epochDimension R i : ℕ) : ℝ))
    (C := 2)
    (n := (LargeScale.updateCount R : ℝ))
    (L := (LargeScale.logScale R : ℝ))
    (d := (LargeScale.epochDimension R i : ℝ))
    hnReal hdNonnegative (by norm_num)
    (LargeScale.updateCount_cast R)
    hdLower
    (certificate.dimension_le_five_sixths i hi)
    certificate.exponent_bound
    (certificate.overflow_budget i hi)
    hthreshold hlower hadvantageUpper'
end

end PegSeparation.LowerBound.MultiphaseLowerBound
