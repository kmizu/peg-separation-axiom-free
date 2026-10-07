import PegSeparation.CFLNotPEG.External.LarsenYuUpperBounds


open scoped BigOperators

namespace PegSeparation.External.LarsenYuNoopNormalization

noncomputable section

open CellProbe

def eraseNoopUpdates
    {Input Query : Type} {wordBits cacheCells maxUpdatedCells : Nat}
    (dataStructure : StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells) :
    StaticStructure Input Query wordBits cacheCells maxUpdatedCells where
  preMemory := dataStructure.preMemory
  updatedAddresses := fun input ↦
    (dataStructure.updatedAddresses input).filter fun address ↦
      dataStructure.updatedWord input address ≠ dataStructure.preMemory address
  updatedWord := dataStructure.updatedWord
  updateBound := fun input ↦
    (Finset.card_filter_le _ _).trans (dataStructure.updateBound input)
  cache := dataStructure.cache
  queryAlgorithm := dataStructure.queryAlgorithm

theorem mem_updatedAddresses_implies_effective
    {Input Query : Type} {wordBits cacheCells maxUpdatedCells : Nat}
    (dataStructure : StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (address : Address wordBits)
    (hmem : address ∈ (eraseNoopUpdates dataStructure).updatedAddresses input) :
    (eraseNoopUpdates dataStructure).updatedWord input address ≠
      (eraseNoopUpdates dataStructure).preMemory address := by
  simpa [eraseNoopUpdates] using (Finset.mem_filter.mp hmem).2

theorem memory_eraseNoopUpdates
    {Input Query : Type} {wordBits cacheCells maxUpdatedCells : Nat}
    (dataStructure : StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) :
    (eraseNoopUpdates dataStructure).memory input =
      dataStructure.memory input := by
  funext address
  unfold StaticStructure.memory
  by_cases hmem : address ∈ dataStructure.updatedAddresses input
  · by_cases heffective :
        dataStructure.updatedWord input address ≠ dataStructure.preMemory address
    · simp [eraseNoopUpdates, hmem, heffective]
    · have heq : dataStructure.updatedWord input address =
          dataStructure.preMemory address := not_ne_iff.mp heffective
      simp [eraseNoopUpdates, hmem, heq]
  · simp [eraseNoopUpdates, hmem]

theorem execute_eraseNoopUpdates
    {Input Query : Type} {wordBits cacheCells maxUpdatedCells : Nat}
    (dataStructure : StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query) :
    (eraseNoopUpdates dataStructure).execute input query =
      dataStructure.execute input query := by
  unfold StaticStructure.execute
  change QueryTree.run ((eraseNoopUpdates dataStructure).memory input)
      (dataStructure.queryAlgorithm query (dataStructure.cache input)) = _
  rw [memory_eraseNoopUpdates]

theorem answer_eraseNoopUpdates
    {Input Query : Type} {wordBits cacheCells maxUpdatedCells : Nat}
    (dataStructure : StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query) :
    (eraseNoopUpdates dataStructure).answer input query =
      dataStructure.answer input query := by
  unfold StaticStructure.answer
  rw [execute_eraseNoopUpdates]

theorem probeTrace_eraseNoopUpdates
    {Input Query : Type} {wordBits cacheCells maxUpdatedCells : Nat}
    (dataStructure : StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query) :
    (eraseNoopUpdates dataStructure).probeTrace input query =
      dataStructure.probeTrace input query := by
  unfold StaticStructure.probeTrace
  rw [execute_eraseNoopUpdates]

theorem solves_eraseNoopUpdates
    {Input Query : Type}
    {wordBits cacheCells maxUpdatedCells : Nat}
    (dataStructure : StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (hsolves : dataStructure.Solves problem) :
    (eraseNoopUpdates dataStructure).Solves problem := by
  intro input query
  rw [answer_eraseNoopUpdates]
  exact hsolves input query

theorem updatedProbeCount_eraseNoopUpdates_le
    {Input Query : Type} {wordBits cacheCells maxUpdatedCells : Nat}
    (dataStructure : StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query) :
    (eraseNoopUpdates dataStructure).updatedProbeCount input query ≤
      dataStructure.updatedProbeCount input query := by
  unfold StaticStructure.updatedProbeCount
  rw [probeTrace_eraseNoopUpdates]
  apply List.countP_mono_left
  intro address _htrace hretained
  have hretainedProp :
      address ∈ (eraseNoopUpdates dataStructure).updatedAddresses input :=
    of_decide_eq_true hretained
  exact decide_eq_true (Finset.mem_filter.mp hretainedProp).1

theorem expectedTotalProbes_eraseNoopUpdates
    {Input Query : Type} [Fintype Input] [Fintype Query]
    {wordBits cacheCells maxUpdatedCells : Nat}
    (dataStructure : StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    (eraseNoopUpdates dataStructure).expectedTotalProbes
        inputDistribution queryDistribution =
      dataStructure.expectedTotalProbes inputDistribution queryDistribution := by
  unfold StaticStructure.expectedTotalProbes
  simp_rw [probeTrace_eraseNoopUpdates]

theorem expectedUpdatedProbes_eraseNoopUpdates_le
    {Input Query : Type} [Fintype Input] [Fintype Query]
    {wordBits cacheCells maxUpdatedCells : Nat}
    (dataStructure : StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    (eraseNoopUpdates dataStructure).expectedUpdatedProbes
        inputDistribution queryDistribution ≤
      dataStructure.expectedUpdatedProbes inputDistribution queryDistribution := by
  unfold StaticStructure.expectedUpdatedProbes
  apply Finset.sum_le_sum
  intro input _hinput
  apply mul_le_mul_of_nonneg_left _ (inputDistribution.mass_nonnegative input)
  apply Finset.sum_le_sum
  intro query _hquery
  apply mul_le_mul_of_nonneg_left _ (queryDistribution.mass_nonnegative query)
  exact_mod_cast updatedProbeCount_eraseNoopUpdates_le dataStructure input query

end

end PegSeparation.External.LarsenYuNoopNormalization
