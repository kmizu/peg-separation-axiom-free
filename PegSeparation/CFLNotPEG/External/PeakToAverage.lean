import PegSeparation.CFLNotPEG.External.Assumptions


open scoped BigOperators

namespace PegSeparation.External.PeakToAverage

noncomputable section

abbrev BoolCube (k : Nat) := Fin k → Bool

def zeroCube (k : Nat) : BoolCube k := fun _ ↦ false

def monomial {k : Nat} (coordinates : Finset (Fin k)) (point : BoolCube k) : ℝ :=
  if ∀ coordinate ∈ coordinates, point coordinate = true then 1 else 0

def evaluate {k : Nat} (coefficient : Finset (Fin k) → ℝ) (point : BoolCube k) : ℝ :=
  ∑ coordinates, coefficient coordinates * monomial coordinates point

def oneFiberSum {k : Nat} (f : BoolCube k → ℝ)
    (coordinates : Finset (Fin k)) : ℝ :=
  ∑ point, if ∀ coordinate ∈ coordinates, point coordinate = true then f point else 0

structure AndCertificate (k degree : Nat) (M : ℝ) where
  coefficient : Finset (Fin k) → ℝ
  degree_le : ∀ coordinates, coefficient coordinates ≠ 0 → coordinates.card ≤ degree
  large_at_zero : M ≤ |evaluate coefficient (zeroCube k)|
  bounded_off_zero : ∀ point ≠ zeroCube k, |evaluate coefficient point| ≤ 1

def AndCertificate.coefficientL1 {k degree : Nat} {M : ℝ}
    (certificate : AndCertificate k degree M) : ℝ :=
  ∑ coordinates, |certificate.coefficient coordinates|

theorem sum_mul_evaluate_eq_sum_coefficient_mul_oneFiberSum
    {k : Nat} (f : BoolCube k → ℝ) (coefficient : Finset (Fin k) → ℝ) :
    ∑ point, f point * evaluate coefficient point =
      ∑ coordinates, coefficient coordinates * oneFiberSum f coordinates := by
  classical
  simp only [evaluate, oneFiberSum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro coordinates _
  apply Finset.sum_congr rfl
  intro point _
  by_cases hpoint : ∀ coordinate ∈ coordinates, point coordinate = true
  · simp [monomial, mul_comm]
  · simp [monomial, hpoint]

theorem exists_large_oneFiberSum_of_certificate
    {k degree : Nat} {M epsilon : ℝ}
    (certificate : AndCertificate k degree M)
    (f : BoolCube k → ℝ)
    (hepsilon : 0 < epsilon)
    (hfL1 : ∑ point, |f point| ≤ 1)
    (hfzero : epsilon ≤ |f (zeroCube k)|)
    (hscale : 2 ≤ M * epsilon) :
    ∃ coordinates : Finset (Fin k),
      coordinates.card ≤ degree ∧
        1 ≤ certificate.coefficientL1 * |oneFiberSum f coordinates| := by
  classical
  let weighted : BoolCube k → ℝ :=
    fun point ↦ f point * evaluate certificate.coefficient point
  have hMpos : 0 < M := by
    by_contra hM
    have hMnonpos : M ≤ 0 := le_of_not_gt hM
    have : M * epsilon ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hMnonpos hepsilon.le
    linarith
  have hzero : 2 ≤ |weighted (zeroCube k)| := by
    dsimp only [weighted]
    rw [abs_mul]
    calc
      2 ≤ M * epsilon := hscale
      _ ≤ |evaluate certificate.coefficient (zeroCube k)| *
          |f (zeroCube k)| :=
        mul_le_mul certificate.large_at_zero hfzero hepsilon.le
          (le_trans hMpos.le certificate.large_at_zero)
      _ = |f (zeroCube k)| *
          |evaluate certificate.coefficient (zeroCube k)| := mul_comm _ _
  have hoffTerm (point : BoolCube k) (hpoint : point ≠ zeroCube k) :
      |weighted point| ≤ |f point| := by
    dsimp only [weighted]
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (certificate.bounded_off_zero point hpoint)
  have hoffsum :
      |∑ point ∈ (Finset.univ.erase (zeroCube k)), weighted point| ≤ 1 := by
    calc
      |∑ point ∈ (Finset.univ.erase (zeroCube k)), weighted point| ≤
          ∑ point ∈ (Finset.univ.erase (zeroCube k)), |weighted point| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ point ∈ (Finset.univ.erase (zeroCube k)), |f point| := by
        apply Finset.sum_le_sum
        intro point hpoint
        exact hoffTerm point (by
          simpa only [Finset.mem_erase, Finset.mem_univ, and_true] using hpoint)
      _ ≤ ∑ point, |f point| := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset _ _) (fun _ _ _ ↦ abs_nonneg _)
      _ ≤ 1 := hfL1
  have hsplit :
      ∑ point, weighted point = weighted (zeroCube k) +
        ∑ point ∈ (Finset.univ.erase (zeroCube k)), weighted point := by
    rw [add_comm]
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ (zeroCube k))).symm
  have hweighted : 1 ≤ |∑ point, weighted point| := by
    let rest : ℝ := ∑ point ∈ (Finset.univ.erase (zeroCube k)), weighted point
    have htriangle : |weighted (zeroCube k)| ≤
        |weighted (zeroCube k) + rest| + |rest| := by
      calc
        |weighted (zeroCube k)| =
            |(weighted (zeroCube k) + rest) + (-rest)| := by ring_nf
        _ ≤ |weighted (zeroCube k) + rest| + |-rest| := abs_add_le _ _
        _ = |weighted (zeroCube k) + rest| + |rest| := by rw [abs_neg]
    rw [hsplit]
    dsimp only [rest] at htriangle ⊢
    linarith
  let support : Finset (Finset (Fin k)) :=
    Finset.univ.filter (fun coordinates ↦ certificate.coefficient coordinates ≠ 0)
  have hsupport : support.Nonempty := by
    by_contra hempty
    have hallzero : ∀ coordinates, certificate.coefficient coordinates = 0 := by
      intro coordinates
      by_contra hnonzero
      have : coordinates ∈ support := by
        simp [support, hnonzero]
      exact hempty ⟨coordinates, this⟩
    have hevalzero : evaluate certificate.coefficient (zeroCube k) = 0 := by
      simp [evaluate, hallzero]
    have : M ≤ 0 := by simpa [hevalzero] using certificate.large_at_zero
    linarith
  obtain ⟨coordinates, hcoordinatesSupport, hmax⟩ :=
    Finset.exists_max_image support (fun Y ↦ |oneFiberSum f Y|) hsupport
  have hcoordinatesNonzero : certificate.coefficient coordinates ≠ 0 := by
    simpa [support] using hcoordinatesSupport
  refine ⟨coordinates, certificate.degree_le coordinates hcoordinatesNonzero, ?_⟩
  have hexpand :
      ∑ point, weighted point =
        ∑ Y, certificate.coefficient Y * oneFiberSum f Y := by
    dsimp only [weighted]
    exact sum_mul_evaluate_eq_sum_coefficient_mul_oneFiberSum f certificate.coefficient
  have hupper :
      |∑ Y, certificate.coefficient Y * oneFiberSum f Y| ≤
        certificate.coefficientL1 * |oneFiberSum f coordinates| := by
    calc
      |∑ Y, certificate.coefficient Y * oneFiberSum f Y| ≤
          ∑ Y, |certificate.coefficient Y * oneFiberSum f Y| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ Y, |certificate.coefficient Y| * |oneFiberSum f Y| := by
        apply Finset.sum_congr rfl
        intro Y _
        rw [abs_mul]
      _ ≤ ∑ Y, |certificate.coefficient Y| * |oneFiberSum f coordinates| := by
        apply Finset.sum_le_sum
        intro Y _
        by_cases hY : certificate.coefficient Y = 0
        · simp [hY]
        · exact mul_le_mul_of_nonneg_left
            (hmax Y (by simp [support, hY])) (abs_nonneg _)
      _ = certificate.coefficientL1 * |oneFiberSum f coordinates| := by
        simp [AndCertificate.coefficientL1, Finset.sum_mul]
  rw [hexpand] at hweighted
  exact hweighted.trans hupper


def differencePattern {Alphabet : Type} [DecidableEq Alphabet] {k : Nat}
    (peak point : Fin k → Alphabet) : BoolCube k :=
  fun coordinate ↦ decide (point coordinate ≠ peak coordinate)

@[simp]
theorem differencePattern_eq_zero_iff
    {Alphabet : Type} [DecidableEq Alphabet] {k : Nat}
    (peak point : Fin k → Alphabet) :
    differencePattern peak point = zeroCube k ↔ point = peak := by
  constructor
  · intro h
    funext coordinate
    have hcoordinate := congrFun h coordinate
    simpa [differencePattern, zeroCube] using hcoordinate
  · rintro rfl
    funext coordinate
    simp [differencePattern, zeroCube]

def booleanized {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} (f : (Fin k → Alphabet) → ℝ) (peak : Fin k → Alphabet) :
    BoolCube k → ℝ :=
  fun pattern ↦
    ∑ point, if differencePattern peak point = pattern then f point else 0

@[simp]
theorem booleanized_zero
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} (f : (Fin k → Alphabet) → ℝ) (peak : Fin k → Alphabet) :
    booleanized f peak (zeroCube k) = f peak := by
  classical
  simp [booleanized, differencePattern_eq_zero_iff]

theorem booleanized_l1_le
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} (f : (Fin k → Alphabet) → ℝ) (peak : Fin k → Alphabet) :
    ∑ pattern, |booleanized f peak pattern| ≤ ∑ point, |f point| := by
  classical
  calc
    ∑ pattern, |booleanized f peak pattern| ≤
        ∑ pattern, ∑ point,
          |if differencePattern peak point = pattern then f point else 0| := by
      apply Finset.sum_le_sum
      intro pattern _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ pattern, ∑ point,
        if differencePattern peak point = pattern then |f point| else 0 := by
      apply Finset.sum_congr rfl
      intro pattern _
      apply Finset.sum_congr rfl
      intro point _
      split <;> simp_all
    _ = ∑ point, ∑ pattern,
        if differencePattern peak point = pattern then |f point| else 0 :=
      Finset.sum_comm
    _ = ∑ point, |f point| := by simp

theorem sum_booleanized_on_predicate
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} (f : (Fin k → Alphabet) → ℝ) (peak : Fin k → Alphabet)
    (predicate : BoolCube k → Prop) [DecidablePred predicate] :
    (∑ pattern, if predicate pattern then booleanized f peak pattern else 0) =
      ∑ point, if predicate (differencePattern peak point) then f point else 0 := by
  classical
  calc
    (∑ pattern, if predicate pattern then booleanized f peak pattern else 0) =
      ∑ pattern, ∑ point,
        if (differencePattern peak point = pattern ∧ predicate pattern)
          then f point else 0 := by
        apply Finset.sum_congr rfl
        intro pattern _
        by_cases hpattern : predicate pattern <;> simp [booleanized, hpattern]
    _ = ∑ point, ∑ pattern,
        if (differencePattern peak point = pattern ∧ predicate pattern)
          then f point else 0 := Finset.sum_comm
    _ = ∑ point, if predicate (differencePattern peak point) then f point else 0 := by
      apply Finset.sum_congr rfl
      intro point _
      rw [Finset.sum_eq_single (differencePattern peak point)]
      · simp
      · intro pattern _ hne
        simp [Ne.symm hne]
      · simp

theorem oneFiberSum_booleanized
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} (f : (Fin k → Alphabet) → ℝ) (peak : Fin k → Alphabet)
    (coordinates : Finset (Fin k)) :
    oneFiberSum (booleanized f peak) coordinates =
      ∑ point, if (∀ coordinate ∈ coordinates,
        point coordinate ≠ peak coordinate) then f point else 0 := by
  classical
  unfold oneFiberSum
  rw [sum_booleanized_on_predicate]
  apply Finset.sum_congr rfl
  intro point _
  congr 1
  simp [differencePattern]

def restrictPoint {Alphabet : Type} {k : Nat} (coordinates : Finset (Fin k))
    (point : Fin k → Alphabet) : (↑coordinates → Alphabet) :=
  fun coordinate ↦ point coordinate.1

def fiberSum {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} (f : (Fin k → Alphabet) → ℝ)
    (coordinates : Finset (Fin k)) (assignment : ↑coordinates → Alphabet) : ℝ :=
  ∑ point, if restrictPoint coordinates point = assignment then f point else 0

def fiberL1 {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} (f : (Fin k → Alphabet) → ℝ)
    (coordinates : Finset (Fin k)) : ℝ :=
  ∑ assignment : ↑coordinates → Alphabet, |fiberSum f coordinates assignment|

theorem fiberL1_nonneg
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} (f : (Fin k → Alphabet) → ℝ)
    (coordinates : Finset (Fin k)) :
    0 ≤ fiberL1 f coordinates := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

theorem sum_fiberSum_on_predicate
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} (f : (Fin k → Alphabet) → ℝ)
    (coordinates : Finset (Fin k))
    (predicate : (↑coordinates → Alphabet) → Prop) [DecidablePred predicate] :
    (∑ assignment, if predicate assignment then fiberSum f coordinates assignment else 0) =
      ∑ point, if predicate (restrictPoint coordinates point) then f point else 0 := by
  classical
  calc
    (∑ assignment, if predicate assignment then fiberSum f coordinates assignment else 0) =
      ∑ assignment, ∑ point,
        if (restrictPoint coordinates point = assignment ∧ predicate assignment)
          then f point else 0 := by
        apply Finset.sum_congr rfl
        intro assignment _
        by_cases hassignment : predicate assignment <;> simp [fiberSum, hassignment]
    _ = ∑ point, ∑ assignment,
        if (restrictPoint coordinates point = assignment ∧ predicate assignment)
          then f point else 0 := Finset.sum_comm
    _ = ∑ point, if predicate (restrictPoint coordinates point) then f point else 0 := by
      apply Finset.sum_congr rfl
      intro point _
      rw [Finset.sum_eq_single (restrictPoint coordinates point)]
      · simp
      · intro assignment _ hne
        simp [Ne.symm hne]
      · simp

theorem abs_oneFiberSum_booleanized_le_fiberL1
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} (f : (Fin k → Alphabet) → ℝ) (peak : Fin k → Alphabet)
    (coordinates : Finset (Fin k)) :
    |oneFiberSum (booleanized f peak) coordinates| ≤ fiberL1 f coordinates := by
  classical
  rw [oneFiberSum_booleanized]
  have hpartition :
      (∑ assignment : ↑coordinates → Alphabet,
          if (∀ coordinate, assignment coordinate ≠ peak coordinate.1) then
            fiberSum f coordinates assignment else 0) =
        ∑ point, if (∀ coordinate ∈ coordinates,
          point coordinate ≠ peak coordinate) then f point else 0 := by
    rw [sum_fiberSum_on_predicate]
    apply Finset.sum_congr rfl
    intro point _
    congr 1
    apply propext
    constructor
    · intro h coordinate hcoordinate
      exact h ⟨coordinate, hcoordinate⟩
    · intro h coordinate
      exact h coordinate.1 coordinate.2
  rw [← hpartition]
  calc
    |∑ assignment : ↑coordinates → Alphabet,
        if (∀ coordinate, assignment coordinate ≠ peak coordinate.1) then
          fiberSum f coordinates assignment else 0| ≤
      ∑ assignment : ↑coordinates → Alphabet,
        |if (∀ coordinate, assignment coordinate ≠ peak coordinate.1) then
          fiberSum f coordinates assignment else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ assignment : ↑coordinates → Alphabet,
        |fiberSum f coordinates assignment| := by
      apply Finset.sum_le_sum
      intro assignment _
      split <;> simp_all
    _ = fiberL1 f coordinates := rfl

theorem exists_large_fiberL1_of_certificate
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k degree : Nat} {M epsilon : ℝ}
    (certificate : AndCertificate k degree M)
    (f : (Fin k → Alphabet) → ℝ)
    (peak : Fin k → Alphabet)
    (hepsilon : 0 < epsilon)
    (hfL1 : ∑ point, |f point| ≤ 1)
    (hfpeak : epsilon ≤ |f peak|)
    (hscale : 2 ≤ M * epsilon) :
    ∃ coordinates : Finset (Fin k),
      coordinates.card ≤ degree ∧
        1 ≤ certificate.coefficientL1 * fiberL1 f coordinates := by
  have hbooleanL1 : ∑ pattern, |booleanized f peak pattern| ≤ 1 :=
    (booleanized_l1_le f peak).trans hfL1
  have hbooleanPeak : epsilon ≤ |booleanized f peak (zeroCube k)| := by
    simpa using hfpeak
  obtain ⟨coordinates, hdegree, hlarge⟩ :=
    exists_large_oneFiberSum_of_certificate certificate (booleanized f peak)
      hepsilon hbooleanL1 hbooleanPeak hscale
  refine ⟨coordinates, hdegree, hlarge.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (abs_oneFiberSum_booleanized_le_fiberL1 f peak coordinates)
    (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)

theorem restrictPoint_univ_injective
    {Alphabet : Type} {k : Nat} :
    Function.Injective
      (restrictPoint (Alphabet := Alphabet) (Finset.univ : Finset (Fin k))) := by
  intro first second hrestriction
  funext coordinate
  exact congrFun hrestriction ⟨coordinate, Finset.mem_univ coordinate⟩

@[simp]
theorem fiberSum_univ_restrictPoint
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} (f : (Fin k → Alphabet) → ℝ) (point : Fin k → Alphabet) :
    fiberSum f Finset.univ (restrictPoint Finset.univ point) = f point := by
  classical
  unfold fiberSum
  rw [Finset.sum_eq_single point]
  · simp
  · intro other _ hother
    have hrestriction :
        restrictPoint Finset.univ other ≠ restrictPoint Finset.univ point :=
      restrictPoint_univ_injective.ne hother
    simp [hrestriction]
  · simp

theorem abs_le_fiberL1_univ
    {Alphabet : Type} [Fintype Alphabet] [DecidableEq Alphabet]
    {k : Nat} (f : (Fin k → Alphabet) → ℝ) (point : Fin k → Alphabet) :
    |f point| ≤ fiberL1 f (Finset.univ : Finset (Fin k)) := by
  let assignment : (↥(Finset.univ : Finset (Fin k)) → Alphabet) :=
    restrictPoint Finset.univ point
  have hsingle :
      |fiberSum f Finset.univ assignment| ≤
        ∑ value : ↥(Finset.univ : Finset (Fin k)) → Alphabet,
          |fiberSum f Finset.univ value| := by
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun value : ↥(Finset.univ : Finset (Fin k)) → Alphabet =>
        |fiberSum f Finset.univ value|)
      (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_univ assignment)
  simpa [fiberL1, assignment] using hsingle

end

end PegSeparation.External.PeakToAverage
