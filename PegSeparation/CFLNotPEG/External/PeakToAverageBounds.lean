import PegSeparation.CFLNotPEG.External.PeakToAverage


namespace PegSeparation.External.PeakToAverageBounds

noncomputable section

open PeakToAverage

theorem exists_fiberL1_ge_inv_of_certificate
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k degree : Nat} {M epsilon bound : ℝ}
    (certificate : AndCertificate k degree M)
    (hbound : certificate.coefficientL1 ≤ bound)
    (hboundPositive : 0 < bound)
    (f : (Fin k → Alphabet) → ℝ)
    (peak : Fin k → Alphabet)
    (hepsilon : 0 < epsilon)
    (hfL1 : ∑ point, |f point| ≤ 1)
    (hfpeak : epsilon ≤ |f peak|)
    (hscale : 2 ≤ M * epsilon) :
    ∃ coordinates : Finset (Fin k),
      coordinates.card ≤ degree ∧
        1 / bound ≤ fiberL1 f coordinates := by
  obtain ⟨coordinates, hdegree, hlarge⟩ :=
    exists_large_fiberL1_of_certificate certificate f peak hepsilon hfL1
      hfpeak hscale
  refine ⟨coordinates, hdegree, ?_⟩
  have hfiber : 0 ≤ fiberL1 f coordinates := fiberL1_nonneg f coordinates
  have hboundedProduct :
      certificate.coefficientL1 * fiberL1 f coordinates ≤
        bound * fiberL1 f coordinates :=
    mul_le_mul_of_nonneg_right hbound hfiber
  apply (div_le_iff₀ hboundPositive).2
  simpa [mul_comm] using hlarge.trans hboundedProduct

theorem exists_full_fiberL1_ge_peak
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} {epsilon : ℝ}
    (f : (Fin k → Alphabet) → ℝ)
    (peak : Fin k → Alphabet)
    (hfpeak : epsilon ≤ |f peak|) :
    ∃ coordinates : Finset (Fin k),
      coordinates.card ≤ k ∧ epsilon ≤ fiberL1 f coordinates := by
  refine ⟨Finset.univ, by simp, ?_⟩
  exact hfpeak.trans (abs_le_fiberL1_univ f peak)

theorem exists_fiberL1_certificate_or_full
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k degree : Nat} {M epsilon bound : ℝ}
    (validRange : Prop)
    (certificate : validRange → AndCertificate k degree M)
    (hbound : ∀ hvalid,
      (certificate hvalid).coefficientL1 ≤ bound)
    (hboundPositive : 0 < bound)
    (f : (Fin k → Alphabet) → ℝ)
    (peak : Fin k → Alphabet)
    (hepsilon : 0 < epsilon)
    (hfL1 : ∑ point, |f point| ≤ 1)
    (hfpeak : epsilon ≤ |f peak|)
    (hscale : validRange → 2 ≤ M * epsilon) :
    ∃ coordinates : Finset (Fin k),
      (validRange ∧ coordinates.card ≤ degree ∧
          1 / bound ≤ fiberL1 f coordinates) ∨
        (¬ validRange ∧ coordinates.card ≤ k ∧
          epsilon ≤ fiberL1 f coordinates) := by
  classical
  by_cases hvalid : validRange
  · obtain ⟨coordinates, hdegree, hfiber⟩ :=
      exists_fiberL1_ge_inv_of_certificate (certificate hvalid)
        (hbound hvalid) hboundPositive f peak hepsilon hfL1 hfpeak
        (hscale hvalid)
    exact ⟨coordinates, Or.inl ⟨hvalid, hdegree, hfiber⟩⟩
  · obtain ⟨coordinates, hdegree, hfiber⟩ :=
      exists_full_fiberL1_ge_peak f peak hfpeak
    exact ⟨coordinates, Or.inr ⟨hvalid, hdegree, hfiber⟩⟩

end

end PegSeparation.External.PeakToAverageBounds
