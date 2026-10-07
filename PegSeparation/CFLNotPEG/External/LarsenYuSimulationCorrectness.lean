import PegSeparation.CFLNotPEG.External.LarsenYuSampledUpdated


namespace PegSeparation.External.LarsenYuSimulationCorrectness

noncomputable section
open LarsenYuBernoulli LarsenYuBernoulliEvents LarsenYuSampledUpdated
  LarsenYuSampledUpdated.CellProbe.StaticStructure

namespace CellProbe.QueryTree

theorem run_eq_of_eq_on_reference_trace
    {wordBits : Nat}
    (tree : CellProbe.QueryTree wordBits)
    (reference candidate : CellProbe.Address wordBits → CellProbe.Word wordBits)
    (hagrees : ∀ address ∈ (tree.run reference).2,
      candidate address = reference address) :
    tree.run candidate = tree.run reference := by
  induction tree with
  | answer value => simp [CellProbe.QueryTree.run]
  | probe address next ih =>
      have haddress : candidate address = reference address := by
        apply hagrees address
        simp [CellProbe.QueryTree.run]
      have htail : ∀ other ∈
          ((next (reference address)).run reference).2,
          candidate other = reference other := by
        intro other hother
        apply hagrees other
        simp [CellProbe.QueryTree.run, hother]
      simp only [CellProbe.QueryTree.run]
      rw [haddress]
      rw [ih (reference address) htail]

end CellProbe.QueryTree

namespace CellProbe.StaticStructure

variable {Input Query : Type} {wordBits cacheCells maxUpdatedCells : Nat}

def sampledMemory
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (selected : Mask (CellProbe.Address wordBits)) :
    CellProbe.Address wordBits → CellProbe.Word wordBits :=
  fun address ↦
    if selected address then dataStructure.memory input address
    else dataStructure.preMemory address

theorem sampledMemory_eq_memory_on_probeTrace_of_includes
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query)
    (selected : Mask (CellProbe.Address wordBits))
    (hincludes : Includes selected
      (probedUpdatedAddresses dataStructure input query))
    (address : CellProbe.Address wordBits)
    (htrace : address ∈ dataStructure.probeTrace input query) :
    sampledMemory dataStructure input selected address =
      dataStructure.memory input address := by
  by_cases hupdated : address ∈ dataStructure.updatedAddresses input
  · have hprobed : address ∈
        probedUpdatedAddresses dataStructure input query := by
      simp [probedUpdatedAddresses, htrace, hupdated]
    have hselected : selected address = true :=
      hincludes address hprobed
    simp [sampledMemory, hselected]
  · simp [sampledMemory, CellProbe.StaticStructure.memory, hupdated]

theorem run_sampledMemory_eq_execute_of_includes
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query)
    (selected : Mask (CellProbe.Address wordBits))
    (hincludes : Includes selected
      (probedUpdatedAddresses dataStructure input query)) :
    (dataStructure.queryAlgorithm query (dataStructure.cache input)).run
        (sampledMemory dataStructure input selected) =
      dataStructure.execute input query := by
  unfold CellProbe.StaticStructure.execute
  apply CellProbe.QueryTree.run_eq_of_eq_on_reference_trace
  intro address htrace
  apply sampledMemory_eq_memory_on_probeTrace_of_includes
    dataStructure input query selected hincludes address
  exact htrace

theorem sampledAnswer_eq_answer_of_includes
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query)
    (selected : Mask (CellProbe.Address wordBits))
    (hincludes : Includes selected
      (probedUpdatedAddresses dataStructure input query)) :
    ((dataStructure.queryAlgorithm query (dataStructure.cache input)).run
      (sampledMemory dataStructure input selected)).1 =
      dataStructure.answer input query := by
  unfold CellProbe.StaticStructure.answer
  rw [run_sampledMemory_eq_execute_of_includes
    dataStructure input query selected hincludes]

theorem sampledTrace_eq_probeTrace_of_includes
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query)
    (selected : Mask (CellProbe.Address wordBits))
    (hincludes : Includes selected
      (probedUpdatedAddresses dataStructure input query)) :
    ((dataStructure.queryAlgorithm query (dataStructure.cache input)).run
      (sampledMemory dataStructure input selected)).2 =
      dataStructure.probeTrace input query := by
  unfold CellProbe.StaticStructure.probeTrace
  rw [run_sampledMemory_eq_execute_of_includes
    dataStructure input query selected hincludes]

theorem sampledAnswer_eq_problem_of_includes
    [Fintype Input] [Fintype Query]
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (hsolves : dataStructure.Solves problem)
    (input : Input) (query : Query)
    (selected : Mask (CellProbe.Address wordBits))
    (hincludes : Includes selected
      (probedUpdatedAddresses dataStructure input query)) :
    ((dataStructure.queryAlgorithm query (dataStructure.cache input)).run
      (sampledMemory dataStructure input selected)).1 =
      problem.value query input := by
  rw [sampledAnswer_eq_answer_of_includes
    dataStructure input query selected hincludes]
  exact hsolves input query

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuSimulationCorrectness
