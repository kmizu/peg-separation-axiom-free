import PegSeparation.CFLNotPEG.External.LarsenYuUpperBounds


namespace PegSeparation.External.LarsenYuCostMonotonicity

noncomputable section

theorem mainTerm_mono_of_cost_le
    {A actualTotal boundedTotal actualUpdated boundedUpdated p : ℝ}
    (hA : 0 ≤ A)
    (hactualTotal : 0 ≤ actualTotal)
    (hactualUpdated : 0 ≤ actualUpdated)
    (htotal : actualTotal ≤ boundedTotal)
    (hupdated : actualUpdated ≤ boundedUpdated)
    (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    Real.rpow 2
        (-A *
          (Real.sqrt
              (boundedTotal *
                (1 + boundedUpdated * log₂ (1 / p))) +
            (1 + boundedUpdated * log₂ (1 / p))) *
          log₂ (1 / p)) ≤
      Real.rpow 2
        (-A *
          (Real.sqrt
              (actualTotal *
                (1 + actualUpdated * log₂ (1 / p))) +
            (1 + actualUpdated * log₂ (1 / p))) *
          log₂ (1 / p)) := by
  let logFactor := log₂ (1 / p)
  let actualLambda := 1 + actualUpdated * logFactor
  let boundedLambda := 1 + boundedUpdated * logFactor
  have hlogFactor : 0 ≤ logFactor :=
    log₂_one_div_nonneg hp hhalf
  have hboundedTotal : 0 ≤ boundedTotal := hactualTotal.trans htotal
  have hboundedUpdated : 0 ≤ boundedUpdated := hactualUpdated.trans hupdated
  have hactualLambda : 0 ≤ actualLambda := by
    dsimp [actualLambda]
    positivity
  have hboundedLambda : 0 ≤ boundedLambda := by
    dsimp [boundedLambda]
    positivity
  have hlambda : actualLambda ≤ boundedLambda := by
    dsimp [actualLambda, boundedLambda]
    exact add_le_add_right
      (mul_le_mul_of_nonneg_right hupdated hlogFactor) 1
  have hproduct : actualTotal * actualLambda ≤
      boundedTotal * boundedLambda :=
    mul_le_mul htotal hlambda hactualLambda hboundedTotal
  have hsqrt : Real.sqrt (actualTotal * actualLambda) ≤
      Real.sqrt (boundedTotal * boundedLambda) :=
    Real.sqrt_le_sqrt hproduct
  have hshape :
      Real.sqrt (actualTotal * actualLambda) + actualLambda ≤
        Real.sqrt (boundedTotal * boundedLambda) + boundedLambda :=
    add_le_add hsqrt hlambda
  have hscaled :
      A * (Real.sqrt (actualTotal * actualLambda) + actualLambda) *
          logFactor ≤
        A * (Real.sqrt (boundedTotal * boundedLambda) + boundedLambda) *
          logFactor :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hshape hA) hlogFactor
  have hexponent :
      -A * (Real.sqrt (boundedTotal * boundedLambda) + boundedLambda) *
          logFactor ≤
        -A * (Real.sqrt (actualTotal * actualLambda) + actualLambda) *
          logFactor := by
    nlinarith
  simpa [actualLambda, boundedLambda, logFactor] using
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      hexponent)

end

end PegSeparation.External.LarsenYuCostMonotonicity
