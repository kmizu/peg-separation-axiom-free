import PegSeparation.CFLNotPEG.External.LarsenYuExperimentPeak
import PegSeparation.CFLNotPEG.External.LarsenYuAdaptiveSampling
import PegSeparation.CFLNotPEG.External.LarsenYuConditionalJensen
import PegSeparation.CFLNotPEG.External.LarsenYuCoinTransport


open scoped BigOperators

namespace PegSeparation.External.LarsenYuExperimentAdvantage

noncomputable section

open LarsenYuBernoulli LarsenYuBernoulliEvents LarsenYuJointCosts
  LarsenYuBaseView LarsenYuExperimentPosterior LarsenYuExperimentPeak
  LarsenYuPosteriorFiltering LarsenYuAdaptiveSampling
  LarsenYuConditionalJensen LarsenYuCoinTransport PeakToAverage
  LarsenYuBaseView.CellProbe.StaticStructure
  LarsenYuExperimentPosterior.CellProbe.StaticStructure
  LarsenYuExperimentPeak.CellProbe.StaticStructure

theorem fiberSum_signedContentMass_eq_restricted
    {Input View Alphabet : Type}
    [Fintype Input] [Fintype View] [Fintype Alphabet]
    [DecidableEq View] [DecidableEq Alphabet]
    {k : Nat}
    (distribution : FiniteDistribution Input)
    (view : Input → View)
    (content : Input → (Fin k → Alphabet))
    (signal : Input → ℝ)
    (selectedView : View)
    (coordinates : Finset (Fin k))
    (assignment : ↑coordinates → Alphabet) :
    fiberSum
        (signedContentMass distribution view content signal selectedView)
        coordinates assignment =
      ∑ input, distribution.mass input *
        (if view input = selectedView ∧
            restrictPoint coordinates (content input) = assignment
          then signal input else 0) := by
  classical
  unfold fiberSum signedContentMass
  calc
    (∑ point, if restrictPoint coordinates point = assignment then
        ∑ input, distribution.mass input *
          (if view input = selectedView ∧ content input = point
            then signal input else 0)
      else 0) =
      ∑ point, ∑ input, distribution.mass input *
        (if restrictPoint coordinates point = assignment ∧
            view input = selectedView ∧ content input = point
          then signal input else 0) := by
        apply Finset.sum_congr rfl
        intro point _hpoint
        by_cases hrestrict :
            restrictPoint coordinates point = assignment <;>
          simp [hrestrict]
    _ = ∑ input, ∑ point, distribution.mass input *
        (if restrictPoint coordinates point = assignment ∧
            view input = selectedView ∧ content input = point
          then signal input else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ input, distribution.mass input *
        (if view input = selectedView ∧
            restrictPoint coordinates (content input) = assignment
          then signal input else 0) := by
      apply Finset.sum_congr rfl
      intro input _hinput
      rw [Fintype.sum_eq_single (content input)]
      · by_cases hview : view input = selectedView <;>
          by_cases hrestrict :
            restrictPoint coordinates (content input) = assignment <;>
          simp [hview, hrestrict]
      · intro other hne
        simp [hne.symm]

theorem coarseMass_mul_fiberL1_normalized_eq_restricted
    {Input View Alphabet : Type}
    [Fintype Input] [Fintype View] [Fintype Alphabet]
    [DecidableEq View] [DecidableEq Alphabet]
    {k : Nat}
    (distribution : FiniteDistribution Input)
    (view : Input → View)
    (content : Input → (Fin k → Alphabet))
    (signal : Input → ℝ)
    (selectedView : View)
    (coordinates : Finset (Fin k)) :
    coarseMass distribution view selectedView *
        fiberL1
          (normalizedSignedContent distribution view content signal selectedView)
          coordinates =
      ∑ assignment : ↑coordinates → Alphabet,
        |∑ input, distribution.mass input *
          (if view input = selectedView ∧
              restrictPoint coordinates (content input) = assignment
            then signal input else 0)| := by
  classical
  let mass := coarseMass distribution view selectedView
  have hmass_nonneg : 0 ≤ mass := coarseMass_nonnegative _ _ _
  by_cases hmass_zero : mass = 0
  · rw [show coarseMass distribution view selectedView = 0 by
      exact hmass_zero, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro assignment _hassignment
    rw [abs_eq_zero]
    apply Finset.sum_eq_zero
    intro input _hinput
    by_cases hview : view input = selectedView
    · have hterm :
          distribution.mass input *
              (if view input = selectedView then 1 else 0) = 0 := by
        have hsum :
            (∑ input, distribution.mass input *
              if view input = selectedView then 1 else 0) = 0 := by
          simpa [mass, coarseMass] using hmass_zero
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun other _ ↦ by
          split <;> simp [distribution.mass_nonnegative other])).mp hsum
            input (Finset.mem_univ input)
      have hinputMass : distribution.mass input = 0 := by
        simpa [hview] using hterm
      simp [hinputMass]
    · simp [hview]
  · have hmass_pos : 0 < mass := lt_of_le_of_ne hmass_nonneg
      (Ne.symm hmass_zero)
    unfold fiberL1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro assignment _hassignment
    have hfiber :
        fiberSum
            (normalizedSignedContent distribution view content signal
              selectedView)
            coordinates assignment =
          (∑ input, distribution.mass input *
            (if view input = selectedView ∧
                restrictPoint coordinates (content input) = assignment
              then signal input else 0)) / mass := by
      calc
        fiberSum
            (normalizedSignedContent distribution view content signal
              selectedView)
            coordinates assignment =
          fiberSum
              (signedContentMass distribution view content signal selectedView)
              coordinates assignment / mass := by
            unfold fiberSum normalizedSignedContent
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro point _hpoint
            by_cases hrestrict :
                restrictPoint coordinates point = assignment <;>
              simp [hrestrict, mass]
        _ = _ := by
          rw [fiberSum_signedContentMass_eq_restricted]
    rw [hfiber, abs_div, abs_of_pos hmass_pos]
    change mass * _ = _
    field_simp

namespace CellProbe.StaticStructure

variable {Input Query : Type} [Fintype Input] [Fintype Query]
  {wordBits cacheCells maxUpdatedCells : Nat}

local instance samplingViewDecidableEq :
    DecidableEq (SamplingView Query wordBits cacheCells) :=
  Classical.decEq _

local instance includesDecidable
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (mask : Mask Coordinate) (required : Finset Coordinate) :
    Decidable (Includes mask required) :=
  LarsenYuBernoulliEvents.includesDecidable mask required

def coordinateAddress
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selectedView : SamplingView Query wordBits cacheCells)
    (index : Fin (simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).card) : CellProbe.Address wordBits :=
  ((simulatedAddresses dataStructure
    selectedView.1.1 selectedView.2).equivFin.symm index).1

def requiredAddresses
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selectedView : SamplingView Query wordBits cacheCells)
    (coordinates : Finset (Fin (simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).card)) :
    Finset (CellProbe.Address wordBits) :=
  coordinates.image (coordinateAddress dataStructure selectedView)

theorem requiredAddresses_card_le
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selectedView : SamplingView Query wordBits cacheCells)
    (coordinates : Finset (Fin (simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).card)) :
    (requiredAddresses dataStructure selectedView coordinates).card ≤
      coordinates.card := by
  exact Finset.card_image_le

def memoryOfPayload
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (payload : CellProbe.Address wordBits → Option (CellProbe.Word wordBits)) :
    CellProbe.Address wordBits → CellProbe.Word wordBits :=
  fun address ↦ (payload address).getD (dataStructure.preMemory address)

theorem memoryOfPayload_baseView_of_selected
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selected : Mask (CellProbe.Address wordBits)) (input : Input)
    (address : CellProbe.Address wordBits)
    (hselected : selected address = true) :
    memoryOfPayload dataStructure (baseView dataStructure selected input).1
        address =
      dataStructure.memory input address := by
  by_cases hupdated : address ∈ dataStructure.updatedAddresses input
  · simp [memoryOfPayload, baseView, CellProbe.StaticStructure.memory,
      hselected, hupdated]
  · simp [memoryOfPayload, baseView, CellProbe.StaticStructure.memory,
      hupdated]

def decodedSelectedContent
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selectedView : SamplingView Query wordBits cacheCells)
    (coordinates : Finset (Fin (simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).card))
    (payload : CellProbe.Address wordBits → Option (CellProbe.Word wordBits)) :
    ↑coordinates → CellProbe.Word wordBits :=
  fun coordinate ↦ memoryOfPayload dataStructure payload
    (coordinateAddress dataStructure selectedView coordinate.1)

theorem decodedSelectedContent_baseView_eq_restrictPoint
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selectedView : SamplingView Query wordBits cacheCells)
    (coordinates : Finset (Fin (simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).card))
    (secondMask : Mask (CellProbe.Address wordBits))
    (sample : SamplingExperiment Input Query wordBits)
    (hincludes : Includes secondMask
      (requiredAddresses dataStructure selectedView coordinates)) :
    decodedSelectedContent dataStructure selectedView coordinates
        (baseView dataStructure secondMask sample.1.1).1 =
      restrictPoint coordinates
        (indexedExperimentContent dataStructure selectedView sample) := by
  funext coordinate
  have hmem : coordinateAddress dataStructure selectedView coordinate.1 ∈
      requiredAddresses dataStructure selectedView coordinates := by
    exact Finset.mem_image.mpr ⟨coordinate.1, coordinate.2, rfl⟩
  have hselected := hincludes
    (coordinateAddress dataStructure selectedView coordinate.1) hmem
  change memoryOfPayload dataStructure
      (baseView dataStructure secondMask sample.1.1).1
      (coordinateAddress dataStructure selectedView coordinate.1) = _
  rw [memoryOfPayload_baseView_of_selected dataStructure secondMask
    sample.1.1 _ hselected]
  rfl


omit [Fintype Input] [Fintype Query] in
theorem problemSignal_eq_neg_character
    (problem : BinaryProblem Input Query)
    (sample : SamplingExperiment Input Query wordBits) :
    problemSignal problem sample =
      - problem.character sample.1.2 sample.1.1 := by
  cases hvalue : problem.value sample.1.2 sample.1.1 <;>
    simp [problemSignal, BinaryProblem.character, hvalue]

theorem experimentRestrictedSignedSum_eq
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (selectedView : SamplingView Query wordBits cacheCells)
    (coordinates : Finset (Fin (simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).card))
    (assignment : ↑coordinates → CellProbe.Word wordBits) :
    (∑ sample : SamplingExperiment Input Query wordBits,
      (samplingExperimentDistribution (wordBits := wordBits)
        inputDistribution queryDistribution p hp hpone).mass sample *
        (if samplingView dataStructure sample = selectedView ∧
            restrictPoint coordinates
              (indexedExperimentContent dataStructure selectedView sample) =
                assignment
          then problemSignal problem sample else 0)) =
      - (queryDistribution.mass selectedView.1.1 *
          (maskDistribution (CellProbe.Address wordBits) p hp hpone).mass
            selectedView.1.2 *
        ∑ input : Input, inputDistribution.mass input *
          (if baseView dataStructure selectedView.1.2 input = selectedView.2 ∧
              restrictPoint coordinates
                (indexedExperimentContent dataStructure selectedView
                  ((input, selectedView.1.1), selectedView.1.2)) = assignment
            then problem.character selectedView.1.1 input else 0)) := by
  classical
  rcases selectedView with ⟨⟨selectedQuery, selectedMask⟩, selectedBase⟩
  unfold samplingExperimentDistribution productDistribution
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  change
    (∑ input : Input, ∑ query : Query,
      ∑ mask : Mask (CellProbe.Address wordBits),
        (inputDistribution.mass input * queryDistribution.mass query) *
          (maskDistribution (CellProbe.Address wordBits) p hp hpone).mass mask *
          (if samplingView dataStructure ((input, query), mask) =
                ((selectedQuery, selectedMask), selectedBase) ∧
              restrictPoint coordinates
                (indexedExperimentContent dataStructure
                  ((selectedQuery, selectedMask), selectedBase)
                  ((input, query), mask)) = assignment
            then problemSignal problem ((input, query), mask) else 0)) =
      - (queryDistribution.mass selectedQuery *
          (maskDistribution (CellProbe.Address wordBits) p hp hpone).mass
            selectedMask *
        ∑ input : Input, inputDistribution.mass input *
          (if baseView dataStructure selectedMask input = selectedBase ∧
              restrictPoint coordinates
                (indexedExperimentContent dataStructure
                  ((selectedQuery, selectedMask), selectedBase)
                  ((input, selectedQuery), selectedMask)) = assignment
            then problem.character selectedQuery input else 0))
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro input _hinput
  rw [Fintype.sum_eq_single selectedQuery]
  · rw [Fintype.sum_eq_single selectedMask]
    · simp only [samplingView, Prod.mk.injEq, true_and]
      by_cases hbase :
          baseView dataStructure selectedMask input = selectedBase
      · by_cases hcontent :
          restrictPoint coordinates
            (indexedExperimentContent dataStructure
              ((selectedQuery, selectedMask), selectedBase)
              ((input, selectedQuery), selectedMask)) = assignment
        · simp [hbase, hcontent, problemSignal_eq_neg_character]
          ring
        · simp [hbase, hcontent]
      · simp [hbase]
    · intro other hne
      simp [samplingView, hne]
  · intro other hne
    simp [samplingView, hne]

theorem experimentPosteriorFiberValue_eq_inputPartition
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (selectedView : SamplingView Query wordBits cacheCells)
    (coordinates : Finset (Fin (simulatedAddresses dataStructure
      selectedView.1.1 selectedView.2).card)) :
    coarseMass
        (samplingExperimentDistribution (wordBits := wordBits)
          inputDistribution queryDistribution p hp hpone)
        (samplingView dataStructure) selectedView *
      fiberL1
        (normalizedSignedContent
          (samplingExperimentDistribution (wordBits := wordBits)
            inputDistribution queryDistribution p hp hpone)
          (samplingView dataStructure)
          (indexedExperimentContent dataStructure selectedView)
          (problemSignal problem) selectedView)
        coordinates =
      queryDistribution.mass selectedView.1.1 *
        (maskDistribution (CellProbe.Address wordBits) p hp hpone).mass
          selectedView.1.2 *
        ∑ assignment : ↑coordinates → CellProbe.Word wordBits,
          |∑ input : Input, inputDistribution.mass input *
            (if baseView dataStructure selectedView.1.2 input = selectedView.2 ∧
                restrictPoint coordinates
                  (indexedExperimentContent dataStructure selectedView
                    ((input, selectedView.1.1), selectedView.1.2)) = assignment
              then problem.character selectedView.1.1 input else 0)| := by
  classical
  rw [coarseMass_mul_fiberL1_normalized_eq_restricted]
  calc
    (∑ assignment : ↑coordinates → CellProbe.Word wordBits,
        |∑ sample,
          (samplingExperimentDistribution (wordBits := wordBits)
            inputDistribution queryDistribution p hp hpone).mass sample *
          (if samplingView dataStructure sample = selectedView ∧
              restrictPoint coordinates
                (indexedExperimentContent dataStructure selectedView sample) =
                  assignment
            then problemSignal problem sample else 0)|) =
      ∑ assignment : ↑coordinates → CellProbe.Word wordBits,
        |- (queryDistribution.mass selectedView.1.1 *
            (maskDistribution (CellProbe.Address wordBits) p hp hpone).mass
              selectedView.1.2 *
          ∑ input : Input, inputDistribution.mass input *
            (if baseView dataStructure selectedView.1.2 input =
                  selectedView.2 ∧
                restrictPoint coordinates
                  (indexedExperimentContent dataStructure selectedView
                    ((input, selectedView.1.1), selectedView.1.2)) = assignment
              then problem.character selectedView.1.1 input else 0))| := by
        apply Finset.sum_congr rfl
        intro assignment _hassignment
        rw [experimentRestrictedSignedSum_eq]
    _ = queryDistribution.mass selectedView.1.1 *
        (maskDistribution (CellProbe.Address wordBits) p hp hpone).mass
          selectedView.1.2 *
        ∑ assignment : ↑coordinates → CellProbe.Word wordBits,
          |∑ input : Input, inputDistribution.mass input *
            (if baseView dataStructure selectedView.1.2 input = selectedView.2 ∧
                restrictPoint coordinates
                  (indexedExperimentContent dataStructure selectedView
                    ((input, selectedView.1.1), selectedView.1.2)) = assignment
              then problem.character selectedView.1.1 input else 0)| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro assignment _hassignment
        rw [abs_neg, abs_mul, abs_mul,
          abs_of_nonneg (queryDistribution.mass_nonnegative selectedView.1.1),
          abs_of_nonneg
            ((maskDistribution (CellProbe.Address wordBits) p hp hpone).mass_nonnegative selectedView.1.2)]


abbrev ExperimentMessage (wordBits cacheCells : Nat) :=
  BaseView wordBits cacheCells ×
    (CellProbe.Address wordBits → Option (CellProbe.Word wordBits))

def experimentEncode
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (coin : Mask (CellProbe.Address wordBits) ×
      Mask (CellProbe.Address wordBits)) (input : Input) :
    ExperimentMessage wordBits cacheCells :=
  (baseView dataStructure coin.1 input,
    (baseView dataStructure coin.2 input).1)

abbrev AdaptiveCoarseMessage
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (coordinates : (selectedView : SamplingView Query wordBits cacheCells) →
      Finset (Fin (simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card)) :=
  Option (Sigma fun selectedView : SamplingView Query wordBits cacheCells ↦
    ↑(coordinates selectedView) → CellProbe.Word wordBits)

local instance adaptiveCoarseMessageDecidableEq
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (coordinates : (selectedView : SamplingView Query wordBits cacheCells) →
      Finset (Fin (simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card)) :
    DecidableEq (AdaptiveCoarseMessage dataStructure coordinates) :=
  Classical.decEq _

def adaptiveCoarseEncode
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (coordinates : (selectedView : SamplingView Query wordBits cacheCells) →
      Finset (Fin (simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card))
    (query : Query) (firstMask secondMask : Mask (CellProbe.Address wordBits))
    (input : Input) : AdaptiveCoarseMessage dataStructure coordinates :=
  let selectedView : SamplingView Query wordBits cacheCells :=
    ((query, firstMask), baseView dataStructure firstMask input)
  if Includes secondMask
      (requiredAddresses dataStructure selectedView (coordinates selectedView))
  then
    some ⟨selectedView,
      restrictPoint (coordinates selectedView)
        (indexedExperimentContent dataStructure selectedView
          ((input, query), firstMask))⟩
  else none

def decodeAdaptiveCoarse
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (coordinates : (selectedView : SamplingView Query wordBits cacheCells) →
      Finset (Fin (simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card))
    (query : Query) (firstMask secondMask : Mask (CellProbe.Address wordBits))
    (message : ExperimentMessage wordBits cacheCells) :
    AdaptiveCoarseMessage dataStructure coordinates :=
  let selectedView : SamplingView Query wordBits cacheCells :=
    ((query, firstMask), message.1)
  if Includes secondMask
      (requiredAddresses dataStructure selectedView (coordinates selectedView))
  then
    some ⟨selectedView,
      decodedSelectedContent dataStructure selectedView
        (coordinates selectedView) message.2⟩
  else none

theorem decodeAdaptiveCoarse_experimentEncode
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (coordinates : (selectedView : SamplingView Query wordBits cacheCells) →
      Finset (Fin (simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card))
    (query : Query) (firstMask secondMask : Mask (CellProbe.Address wordBits))
    (input : Input) :
    decodeAdaptiveCoarse dataStructure coordinates query firstMask secondMask
        (experimentEncode dataStructure (firstMask, secondMask) input) =
      adaptiveCoarseEncode dataStructure coordinates query firstMask secondMask
        input := by
  classical
  let selectedView : SamplingView Query wordBits cacheCells :=
    ((query, firstMask), baseView dataStructure firstMask input)
  by_cases hincludes : Includes secondMask
      (requiredAddresses dataStructure selectedView (coordinates selectedView))
  · have hcontent :=
      decodedSelectedContent_baseView_eq_restrictPoint
        dataStructure selectedView (coordinates selectedView) secondMask
          ((input, query), firstMask) hincludes
    have hsigma := congrArg
      (fun content ↦ (some ⟨selectedView, content⟩ :
        AdaptiveCoarseMessage dataStructure coordinates)) hcontent
    simpa [decodeAdaptiveCoarse, experimentEncode, adaptiveCoarseEncode,
      selectedView, hincludes] using hsigma
  · simp [decodeAdaptiveCoarse, experimentEncode, adaptiveCoarseEncode,
      selectedView, hincludes]

theorem adaptiveCoarse_someFiber_eq
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (coordinates : (selectedView : SamplingView Query wordBits cacheCells) →
      Finset (Fin (simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card))
    (query : Query) (firstMask secondMask : Mask (CellProbe.Address wordBits))
    (selectedBase : BaseView wordBits cacheCells)
    (assignment : ↑(coordinates ((query, firstMask), selectedBase)) →
      CellProbe.Word wordBits)
    (hincludes : Includes secondMask
      (requiredAddresses dataStructure ((query, firstMask), selectedBase)
        (coordinates ((query, firstMask), selectedBase)))) :
    (∑ input : Input, inputDistribution.mass input *
      (if adaptiveCoarseEncode dataStructure coordinates query firstMask
          secondMask input =
          (some ⟨((query, firstMask), selectedBase), assignment⟩ :
            AdaptiveCoarseMessage dataStructure coordinates)
        then problem.character query input else 0)) =
      ∑ input : Input, inputDistribution.mass input *
        (if baseView dataStructure firstMask input = selectedBase ∧
            restrictPoint (coordinates ((query, firstMask), selectedBase))
              (indexedExperimentContent dataStructure
                ((query, firstMask), selectedBase)
                ((input, query), firstMask)) = assignment
          then problem.character query input else 0) := by
  classical
  apply Finset.sum_congr rfl
  intro input _hinput
  by_cases hbase : baseView dataStructure firstMask input = selectedBase
  · subst selectedBase
    simp [adaptiveCoarseEncode, hincludes]
  · let actualView : SamplingView Query wordBits cacheCells :=
      ((query, firstMask), baseView dataStructure firstMask input)
    by_cases hactual : Includes secondMask
        (requiredAddresses dataStructure actualView (coordinates actualView))
    · simp [adaptiveCoarseEncode, actualView, hactual, hbase]
    · simp [adaptiveCoarseEncode, actualView, hactual, hbase]

theorem includedBaseViewPartitions_le_adaptiveCoarsePartition
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (coordinates : (selectedView : SamplingView Query wordBits cacheCells) →
      Finset (Fin (simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card))
    (query : Query) (firstMask secondMask : Mask (CellProbe.Address wordBits)) :
    (∑ selectedBase : BaseView wordBits cacheCells,
      if Includes secondMask
          (requiredAddresses dataStructure ((query, firstMask), selectedBase)
            (coordinates ((query, firstMask), selectedBase)))
      then
        ∑ assignment :
            ↑(coordinates ((query, firstMask), selectedBase)) →
              CellProbe.Word wordBits,
          |∑ input : Input, inputDistribution.mass input *
            (if baseView dataStructure firstMask input = selectedBase ∧
                restrictPoint
                    (coordinates ((query, firstMask), selectedBase))
                    (indexedExperimentContent dataStructure
                      ((query, firstMask), selectedBase)
                      ((input, query), firstMask)) = assignment
              then problem.character query input else 0)|
      else 0) ≤
      ∑ coarseMessage : AdaptiveCoarseMessage dataStructure coordinates,
        |∑ input : Input, inputDistribution.mass input *
          (if adaptiveCoarseEncode dataStructure coordinates query firstMask
              secondMask input = coarseMessage
            then problem.character query input else 0)| := by
  classical
  let term : AdaptiveCoarseMessage dataStructure coordinates → ℝ :=
    fun coarseMessage ↦
      |∑ input : Input, inputDistribution.mass input *
        (if adaptiveCoarseEncode dataStructure coordinates query firstMask
            secondMask input = coarseMessage
          then problem.character query input else 0)|
  let grouped : SamplingView Query wordBits cacheCells → ℝ :=
    fun selectedView ↦
      ∑ assignment : ↑(coordinates selectedView) → CellProbe.Word wordBits,
        term (some ⟨selectedView, assignment⟩)
  have hterm_nonnegative
      (coarseMessage : AdaptiveCoarseMessage dataStructure coordinates) :
      0 ≤ term coarseMessage := by
    exact abs_nonneg _
  have hgrouped_nonnegative (selectedView) : 0 ≤ grouped selectedView := by
    exact Finset.sum_nonneg fun _ _ ↦ hterm_nonnegative _
  change _ ≤ ∑ coarseMessage, term coarseMessage
  calc
    _ ≤ ∑ selectedBase : BaseView wordBits cacheCells,
        grouped ((query, firstMask), selectedBase) := by
      apply Finset.sum_le_sum
      intro selectedBase _hselectedBase
      by_cases hincludes : Includes secondMask
          (requiredAddresses dataStructure ((query, firstMask), selectedBase)
            (coordinates ((query, firstMask), selectedBase)))
      · rw [if_pos hincludes]
        dsimp only [grouped, term]
        apply Finset.sum_le_sum
        intro assignment _hassignment
        rw [adaptiveCoarse_someFiber_eq dataStructure problem
          inputDistribution coordinates query firstMask secondMask selectedBase
          assignment hincludes]
      · rw [if_neg hincludes]
        exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    _ ≤ ∑ selectedView : SamplingView Query wordBits cacheCells,
        grouped selectedView := by
      rw [show
        (∑ selectedView : SamplingView Query wordBits cacheCells,
            grouped selectedView) =
          ∑ pair : Query × Mask (CellProbe.Address wordBits),
            ∑ selectedBase : BaseView wordBits cacheCells,
              grouped (pair, selectedBase) by
        exact Fintype.sum_prod_type grouped]
      exact Finset.single_le_sum
        (fun pair _ ↦ Finset.sum_nonneg fun selectedBase _ ↦
          hgrouped_nonnegative (pair, selectedBase))
        (Finset.mem_univ (query, firstMask))
    _ ≤ term none + ∑ selectedView : SamplingView Query wordBits cacheCells,
        grouped selectedView := by
      exact le_add_of_nonneg_left (hterm_nonnegative none)
    _ = ∑ coarseMessage, term coarseMessage := by
      symm
      rw [Fintype.sum_option, Fintype.sum_sigma]

theorem adaptiveCoarsePartition_le_experimentMessagePartition
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (coordinates : (selectedView : SamplingView Query wordBits cacheCells) →
      Finset (Fin (simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card))
    (query : Query) (firstMask secondMask : Mask (CellProbe.Address wordBits)) :
    (∑ coarseMessage : AdaptiveCoarseMessage dataStructure coordinates,
        |∑ input : Input, inputDistribution.mass input *
          (if adaptiveCoarseEncode dataStructure coordinates query firstMask
              secondMask input = coarseMessage
            then problem.character query input else 0)|) ≤
      ∑ fineMessage : ExperimentMessage wordBits cacheCells,
        |∑ input : Input, inputDistribution.mass input *
          (if experimentEncode dataStructure (firstMask, secondMask) input =
              fineMessage
            then problem.character query input else 0)| := by
  classical
  exact partitionL1_mono_of_factor
    inputDistribution.mass (problem.character query)
    (adaptiveCoarseEncode dataStructure coordinates query firstMask secondMask)
    (experimentEncode dataStructure (firstMask, secondMask))
    (decodeAdaptiveCoarse dataStructure coordinates query firstMask secondMask)
    (decodeAdaptiveCoarse_experimentEncode dataStructure coordinates query
      firstMask secondMask)


theorem includedExperimentViews_le_fixedSecondMaskPartition
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (coordinates : (selectedView : SamplingView Query wordBits cacheCells) →
      Finset (Fin (simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card))
    (secondMask : Mask (CellProbe.Address wordBits)) :
    (∑ selectedView : SamplingView Query wordBits cacheCells,
      if Includes secondMask
          (requiredAddresses dataStructure selectedView
            (coordinates selectedView))
      then
        coarseMass
            (samplingExperimentDistribution (wordBits := wordBits)
              inputDistribution queryDistribution p hp hpone)
            (samplingView dataStructure) selectedView *
          fiberL1
            (normalizedSignedContent
              (samplingExperimentDistribution (wordBits := wordBits)
                inputDistribution queryDistribution p hp hpone)
              (samplingView dataStructure)
              (indexedExperimentContent dataStructure selectedView)
              (problemSignal problem) selectedView)
            (coordinates selectedView)
      else 0) ≤
      ∑ pair : Query × Mask (CellProbe.Address wordBits),
        queryDistribution.mass pair.1 *
          (maskDistribution (CellProbe.Address wordBits) p hp hpone).mass
            pair.2 *
          ∑ fineMessage : ExperimentMessage wordBits cacheCells,
            |∑ input : Input, inputDistribution.mass input *
              (if experimentEncode dataStructure (pair.2, secondMask) input =
                  fineMessage
                then problem.character pair.1 input else 0)| := by
  classical
  rw [show
    (∑ selectedView : SamplingView Query wordBits cacheCells,
      if Includes secondMask
          (requiredAddresses dataStructure selectedView
            (coordinates selectedView))
      then
        coarseMass
            (samplingExperimentDistribution (wordBits := wordBits)
              inputDistribution queryDistribution p hp hpone)
            (samplingView dataStructure) selectedView *
          fiberL1
            (normalizedSignedContent
              (samplingExperimentDistribution (wordBits := wordBits)
                inputDistribution queryDistribution p hp hpone)
              (samplingView dataStructure)
              (indexedExperimentContent dataStructure selectedView)
              (problemSignal problem) selectedView)
            (coordinates selectedView)
      else 0) =
      ∑ pair : Query × Mask (CellProbe.Address wordBits),
        ∑ selectedBase : BaseView wordBits cacheCells,
          if Includes secondMask
              (requiredAddresses dataStructure (pair, selectedBase)
                (coordinates (pair, selectedBase)))
          then
            coarseMass
                (samplingExperimentDistribution (wordBits := wordBits)
                  inputDistribution queryDistribution p hp hpone)
                (samplingView dataStructure) (pair, selectedBase) *
              fiberL1
                (normalizedSignedContent
                  (samplingExperimentDistribution (wordBits := wordBits)
                    inputDistribution queryDistribution p hp hpone)
                  (samplingView dataStructure)
                  (indexedExperimentContent dataStructure
                    (pair, selectedBase))
                  (problemSignal problem) (pair, selectedBase))
                (coordinates (pair, selectedBase))
          else 0 by
    exact Fintype.sum_prod_type _]
  apply Finset.sum_le_sum
  intro pair _hpair
  rcases pair with ⟨query, firstMask⟩
  let factor := queryDistribution.mass query *
    (maskDistribution (CellProbe.Address wordBits) p hp hpone).mass firstMask
  let localFiber (selectedBase : BaseView wordBits cacheCells) : ℝ :=
    ∑ assignment :
        ↑(coordinates ((query, firstMask), selectedBase)) →
          CellProbe.Word wordBits,
      |∑ input : Input, inputDistribution.mass input *
        (if baseView dataStructure firstMask input = selectedBase ∧
            restrictPoint (coordinates ((query, firstMask), selectedBase))
              (indexedExperimentContent dataStructure
                ((query, firstMask), selectedBase)
                ((input, query), firstMask)) = assignment
          then problem.character query input else 0)|
  calc
    (∑ selectedBase : BaseView wordBits cacheCells,
      if Includes secondMask
          (requiredAddresses dataStructure ((query, firstMask), selectedBase)
            (coordinates ((query, firstMask), selectedBase)))
      then
        coarseMass
            (samplingExperimentDistribution (wordBits := wordBits)
              inputDistribution queryDistribution p hp hpone)
            (samplingView dataStructure) ((query, firstMask), selectedBase) *
          fiberL1
            (normalizedSignedContent
              (samplingExperimentDistribution (wordBits := wordBits)
                inputDistribution queryDistribution p hp hpone)
              (samplingView dataStructure)
              (indexedExperimentContent dataStructure
                ((query, firstMask), selectedBase))
              (problemSignal problem) ((query, firstMask), selectedBase))
            (coordinates ((query, firstMask), selectedBase))
      else 0) =
        factor * ∑ selectedBase : BaseView wordBits cacheCells,
          if Includes secondMask
              (requiredAddresses dataStructure ((query, firstMask), selectedBase)
                (coordinates ((query, firstMask), selectedBase)))
          then localFiber selectedBase else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro selectedBase _hselectedBase
      by_cases hincludes : Includes secondMask
          (requiredAddresses dataStructure ((query, firstMask), selectedBase)
            (coordinates ((query, firstMask), selectedBase)))
      · simp only [hincludes, if_true]
        exact experimentPosteriorFiberValue_eq_inputPartition
          dataStructure problem inputDistribution queryDistribution p hp hpone
          ((query, firstMask), selectedBase)
          (coordinates ((query, firstMask), selectedBase))
      · simp [hincludes]
    _ ≤ factor *
        (∑ coarseMessage : AdaptiveCoarseMessage dataStructure coordinates,
          |∑ input : Input, inputDistribution.mass input *
            (if adaptiveCoarseEncode dataStructure coordinates query firstMask
                secondMask input = coarseMessage
              then problem.character query input else 0)|) := by
      apply mul_le_mul_of_nonneg_left
      · exact includedBaseViewPartitions_le_adaptiveCoarsePartition
          dataStructure problem inputDistribution coordinates query firstMask
            secondMask
      · exact mul_nonneg
          (queryDistribution.mass_nonnegative query)
          (FiniteDistribution.mass_nonnegative
            (maskDistribution (CellProbe.Address wordBits) p hp hpone) firstMask)
    _ ≤ factor *
        (∑ fineMessage : ExperimentMessage wordBits cacheCells,
          |∑ input : Input, inputDistribution.mass input *
            (if experimentEncode dataStructure (firstMask, secondMask) input =
                fineMessage
              then problem.character query input else 0)|) := by
      apply mul_le_mul_of_nonneg_left
      · exact adaptiveCoarsePartition_le_experimentMessagePartition
          dataStructure problem inputDistribution coordinates query firstMask
            secondMask
      · exact mul_nonneg
          (queryDistribution.mass_nonnegative query)
          (FiniteDistribution.mass_nonnegative
            (maskDistribution (CellProbe.Address wordBits) p hp hpone) firstMask)


theorem pow_degree_mul_selectedFiberSum_le_outcomeStructuredAdvantage
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query)
    (p : ℝ) (hp : 0 ≤ p) (hpone : p ≤ 1)
    (degree : Nat)
    (coordinates : (selectedView : SamplingView Query wordBits cacheCells) →
      Finset (Fin (simulatedAddresses dataStructure
        selectedView.1.1 selectedView.2).card))
    (hdegree : ∀ selectedView, (coordinates selectedView).card ≤ degree) :
    p ^ degree *
      ∑ selectedView : SamplingView Query wordBits cacheCells,
        coarseMass
            (samplingExperimentDistribution (wordBits := wordBits)
              inputDistribution queryDistribution p hp hpone)
            (samplingView dataStructure) selectedView *
          fiberL1
            (normalizedSignedContent
              (samplingExperimentDistribution (wordBits := wordBits)
                inputDistribution queryDistribution p hp hpone)
              (samplingView dataStructure)
              (indexedExperimentContent dataStructure selectedView)
              (problemSignal problem) selectedView)
            (coordinates selectedView) ≤
      outcomeStructuredAdvantage
        (productDistribution
          (Mask (CellProbe.Address wordBits))
          (Mask (CellProbe.Address wordBits))
          (maskDistribution (CellProbe.Address wordBits) p hp hpone)
          (maskDistribution (CellProbe.Address wordBits) p hp hpone))
        (experimentEncode dataStructure)
        problem inputDistribution queryDistribution := by
  classical
  let maskDist :=
    maskDistribution (CellProbe.Address wordBits) p hp hpone
  let viewValue : SamplingView Query wordBits cacheCells → ℝ :=
    fun selectedView ↦
      coarseMass
          (samplingExperimentDistribution (wordBits := wordBits)
            inputDistribution queryDistribution p hp hpone)
          (samplingView dataStructure) selectedView *
        fiberL1
          (normalizedSignedContent
            (samplingExperimentDistribution (wordBits := wordBits)
              inputDistribution queryDistribution p hp hpone)
            (samplingView dataStructure)
            (indexedExperimentContent dataStructure selectedView)
            (problemSignal problem) selectedView)
          (coordinates selectedView)
  let fine :
      Query → Mask (CellProbe.Address wordBits) →
        Mask (CellProbe.Address wordBits) → ℝ :=
    fun query firstMask secondMask ↦
      ∑ fineMessage : ExperimentMessage wordBits cacheCells,
        |∑ input : Input, inputDistribution.mass input *
          (if experimentEncode dataStructure (firstMask, secondMask) input =
              fineMessage
            then problem.character query input else 0)|
  change p ^ degree * ∑ selectedView, viewValue selectedView ≤ _
  calc
    _ ≤ ∑ secondMask : Mask (CellProbe.Address wordBits),
        maskDist.mass secondMask *
          ∑ selectedView : SamplingView Query wordBits cacheCells,
            if Includes secondMask
                (requiredAddresses dataStructure selectedView
                  (coordinates selectedView))
            then viewValue selectedView else 0 := by
      apply pow_degree_mul_sum_le_maskAverage
      · intro selectedView
        exact (requiredAddresses_card_le dataStructure selectedView
          (coordinates selectedView)).trans (hdegree selectedView)
      · intro selectedView
        exact mul_nonneg
          (coarseMass_nonnegative _ _ _)
          (fiberL1_nonneg _ _)
    _ ≤ ∑ secondMask : Mask (CellProbe.Address wordBits),
        maskDist.mass secondMask *
          ∑ pair : Query × Mask (CellProbe.Address wordBits),
            queryDistribution.mass pair.1 * maskDist.mass pair.2 *
              fine pair.1 pair.2 secondMask := by
      apply Finset.sum_le_sum
      intro secondMask _hsecondMask
      apply mul_le_mul_of_nonneg_left
      · exact includedExperimentViews_le_fixedSecondMaskPartition
          dataStructure problem inputDistribution queryDistribution p hp hpone
            coordinates secondMask
      · exact maskDist.mass_nonnegative secondMask
    _ = outcomeStructuredAdvantage
        (productDistribution
          (Mask (CellProbe.Address wordBits))
          (Mask (CellProbe.Address wordBits))
          (maskDistribution (CellProbe.Address wordBits) p hp hpone)
          (maskDistribution (CellProbe.Address wordBits) p hp hpone))
        (experimentEncode dataStructure)
        problem inputDistribution queryDistribution := by
      unfold outcomeStructuredAdvantage productDistribution
      change
        (∑ secondMask : Mask (CellProbe.Address wordBits),
          maskDist.mass secondMask *
            ∑ pair : Query × Mask (CellProbe.Address wordBits),
              queryDistribution.mass pair.1 * maskDist.mass pair.2 *
                fine pair.1 pair.2 secondMask) =
        ∑ coin : Mask (CellProbe.Address wordBits) ×
            Mask (CellProbe.Address wordBits),
          (maskDist.mass coin.1 * maskDist.mass coin.2) *
            ∑ query : Query, queryDistribution.mass query *
              fine query coin.1 coin.2
      have hpair (secondMask : Mask (CellProbe.Address wordBits)) :
          (∑ pair : Query × Mask (CellProbe.Address wordBits),
            queryDistribution.mass pair.1 * maskDist.mass pair.2 *
              fine pair.1 pair.2 secondMask) =
            ∑ query : Query,
              ∑ firstMask : Mask (CellProbe.Address wordBits),
                queryDistribution.mass query * maskDist.mass firstMask *
                  fine query firstMask secondMask :=
        Fintype.sum_prod_type _
      simp_rw [hpair]
      rw [show
        (∑ coin : Mask (CellProbe.Address wordBits) ×
            Mask (CellProbe.Address wordBits),
          (maskDist.mass coin.1 * maskDist.mass coin.2) *
            ∑ query : Query, queryDistribution.mass query *
              fine query coin.1 coin.2) =
          ∑ firstMask : Mask (CellProbe.Address wordBits),
            ∑ secondMask : Mask (CellProbe.Address wordBits),
              (maskDist.mass firstMask * maskDist.mass secondMask) *
                ∑ query : Query, queryDistribution.mass query *
                  fine query firstMask secondMask by
        exact Fintype.sum_prod_type _]
      calc
        (∑ secondMask, maskDist.mass secondMask *
          ∑ query, ∑ firstMask,
            queryDistribution.mass query * maskDist.mass firstMask *
              fine query firstMask secondMask) =
          ∑ secondMask, ∑ query, ∑ firstMask,
            maskDist.mass secondMask *
              (queryDistribution.mass query * maskDist.mass firstMask *
                fine query firstMask secondMask) := by
            apply Finset.sum_congr rfl
            intro secondMask _hsecondMask
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro query _hquery
            rw [Finset.mul_sum]
        _ = ∑ secondMask, ∑ firstMask, ∑ query,
            maskDist.mass secondMask *
              (queryDistribution.mass query * maskDist.mass firstMask *
                fine query firstMask secondMask) := by
            apply Finset.sum_congr rfl
            intro secondMask _hsecondMask
            rw [Finset.sum_comm]
        _ = ∑ firstMask, ∑ secondMask, ∑ query,
            maskDist.mass secondMask *
              (queryDistribution.mass query * maskDist.mass firstMask *
                fine query firstMask secondMask) := by
            rw [Finset.sum_comm]
        _ = ∑ firstMask, ∑ secondMask,
            (maskDist.mass firstMask * maskDist.mass secondMask) *
              ∑ query, queryDistribution.mass query *
                fine query firstMask secondMask := by
            apply Finset.sum_congr rfl
            intro firstMask _hfirstMask
            apply Finset.sum_congr rfl
            intro secondMask _hsecondMask
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro query _hquery
            ring

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuExperimentAdvantage
