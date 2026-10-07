import PegSeparation.CFLNotPEG.External.LarsenYuSimulationCorrectness


namespace PegSeparation.External.LarsenYuBaseView

noncomputable section

open LarsenYuBernoulli LarsenYuBernoulliEvents LarsenYuSampledUpdated
  LarsenYuSampledUpdated.CellProbe.StaticStructure
  LarsenYuSimulationCorrectness
  LarsenYuSimulationCorrectness.CellProbe.StaticStructure

abbrev BaseView (wordBits cacheCells : Nat) :=
  (CellProbe.Address wordBits → Option (CellProbe.Word wordBits)) ×
    (Fin cacheCells → CellProbe.Word wordBits)

namespace CellProbe.StaticStructure

variable {Input Query : Type} {wordBits cacheCells maxUpdatedCells : Nat}

def baseView
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selected : Mask (CellProbe.Address wordBits)) (input : Input) :
    BaseView wordBits cacheCells :=
  (fun address ↦
    if selected address ∧ address ∈ dataStructure.updatedAddresses input then
      some (dataStructure.updatedWord input address)
    else none,
   dataStructure.cache input)

def memoryOfBaseView
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (view : BaseView wordBits cacheCells) :
    CellProbe.Address wordBits → CellProbe.Word wordBits :=
  fun address ↦ (view.1 address).getD (dataStructure.preMemory address)

theorem memoryOfBaseView_baseView
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selected : Mask (CellProbe.Address wordBits)) (input : Input) :
    memoryOfBaseView dataStructure (baseView dataStructure selected input) =
      sampledMemory dataStructure input selected := by
  funext address
  cases hselected : selected address <;>
    by_cases hupdated : address ∈ dataStructure.updatedAddresses input <;>
      simp [memoryOfBaseView, baseView, sampledMemory,
        CellProbe.StaticStructure.memory, hselected, hupdated]

def simulateFromBaseView
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (query : Query) (view : BaseView wordBits cacheCells) :
    Bool × List (CellProbe.Address wordBits) :=
  (dataStructure.queryAlgorithm query view.2).run
    (memoryOfBaseView dataStructure view)

theorem simulateFrom_generated_baseView
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selected : Mask (CellProbe.Address wordBits))
    (input : Input) (query : Query) :
    simulateFromBaseView dataStructure query
        (baseView dataStructure selected input) =
      (dataStructure.queryAlgorithm query (dataStructure.cache input)).run
        (sampledMemory dataStructure input selected) := by
  unfold simulateFromBaseView
  rw [memoryOfBaseView_baseView]
  rfl

def simulatedAddresses
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (query : Query) (view : BaseView wordBits cacheCells) :
    Finset (CellProbe.Address wordBits) :=
  (simulateFromBaseView dataStructure query view).2.toFinset

def trueContent
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (addresses : Finset (CellProbe.Address wordBits)) (input : Input) :
    ↑addresses → CellProbe.Word wordBits :=
  fun address ↦ dataStructure.memory input address

def usedContent
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (query : Query) (view : BaseView wordBits cacheCells) :
    ↑(simulatedAddresses dataStructure query view) → CellProbe.Word wordBits :=
  fun address ↦ memoryOfBaseView dataStructure view address

theorem execute_eq_simulateFromBaseView_of_agrees
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query) (view : BaseView wordBits cacheCells)
    (hcache : dataStructure.cache input = view.2)
    (hagrees : ∀ address ∈ simulatedAddresses dataStructure query view,
      dataStructure.memory input address =
        memoryOfBaseView dataStructure view address) :
    dataStructure.execute input query =
      simulateFromBaseView dataStructure query view := by
  unfold CellProbe.StaticStructure.execute simulateFromBaseView
  rw [hcache]
  apply CellProbe.QueryTree.run_eq_of_eq_on_reference_trace
  intro address htrace
  apply hagrees address
  simpa [simulatedAddresses, simulateFromBaseView] using htrace

theorem execute_eq_simulateFromBaseView_of_content_eq
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query) (view : BaseView wordBits cacheCells)
    (hcache : dataStructure.cache input = view.2)
    (hcontent : trueContent dataStructure
        (simulatedAddresses dataStructure query view) input =
      usedContent dataStructure query view) :
    dataStructure.execute input query =
      simulateFromBaseView dataStructure query view := by
  apply execute_eq_simulateFromBaseView_of_agrees
    dataStructure input query view hcache
  intro address haddress
  exact congrFun hcontent ⟨address, haddress⟩

theorem execute_eq_simulateFromBaseView_of_baseView_eq_of_content_eq
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selected : Mask (CellProbe.Address wordBits))
    (input : Input) (query : Query) (view : BaseView wordBits cacheCells)
    (hview : baseView dataStructure selected input = view)
    (hcontent : trueContent dataStructure
        (simulatedAddresses dataStructure query view) input =
      usedContent dataStructure query view) :
    dataStructure.execute input query =
      simulateFromBaseView dataStructure query view := by
  apply execute_eq_simulateFromBaseView_of_content_eq
    dataStructure input query view
  · exact congrArg Prod.snd hview
  · exact hcontent

theorem trueContent_eq_usedContent_of_includes
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (selected : Mask (CellProbe.Address wordBits))
    (input : Input) (query : Query)
    (hincludes : Includes selected
      (probedUpdatedAddresses dataStructure input query)) :
    trueContent dataStructure
        (simulatedAddresses dataStructure query
          (baseView dataStructure selected input)) input =
      usedContent dataStructure query
        (baseView dataStructure selected input) := by
  funext address
  have hsimulation :
      simulateFromBaseView dataStructure query
          (baseView dataStructure selected input) =
        dataStructure.execute input query := by
    rw [simulateFrom_generated_baseView]
    exact run_sampledMemory_eq_execute_of_includes
      dataStructure input query selected hincludes
  have haddress : (address : CellProbe.Address wordBits) ∈
      (simulateFromBaseView dataStructure query
        (baseView dataStructure selected input)).2 := by
    exact List.mem_toFinset.mp address.property
  have htraceEq :
      (simulateFromBaseView dataStructure query
        (baseView dataStructure selected input)).2 =
        (dataStructure.execute input query).2 :=
    congrArg Prod.snd hsimulation
  rw [htraceEq] at haddress
  have htrace : (address : CellProbe.Address wordBits) ∈
      dataStructure.probeTrace input query := by
    simpa [CellProbe.StaticStructure.probeTrace] using haddress
  have hagrees := sampledMemory_eq_memory_on_probeTrace_of_includes
    dataStructure input query selected hincludes address htrace
  have hmemory := congrFun
    (memoryOfBaseView_baseView dataStructure selected input) address
  exact (hmemory.trans hagrees).symm

theorem problemValue_eq_simulatedAnswer_of_peakContent
    [Fintype Input] [Fintype Query]
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (problem : BinaryProblem Input Query)
    (hsolves : dataStructure.Solves problem)
    (selected : Mask (CellProbe.Address wordBits))
    (input : Input) (query : Query) (view : BaseView wordBits cacheCells)
    (hview : baseView dataStructure selected input = view)
    (hcontent : trueContent dataStructure
        (simulatedAddresses dataStructure query view) input =
      usedContent dataStructure query view) :
    problem.value query input =
      (simulateFromBaseView dataStructure query view).1 := by
  rw [← hsolves input query]
  unfold CellProbe.StaticStructure.answer
  rw [execute_eq_simulateFromBaseView_of_baseView_eq_of_content_eq
    dataStructure selected input query view hview hcontent]

end CellProbe.StaticStructure

end

end PegSeparation.External.LarsenYuBaseView
