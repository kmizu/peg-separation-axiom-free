import PegSeparation.CFLNotPEG.External.Assumptions
import PegSeparation.Common.Recognition
import PegSeparation.CFLNotPEG.Witness.LanguageCFG
import PegSeparation.CFLNotPEG.Witness.HardSlice
import PegSeparation.CFLNotPEG.Reduction.MultiphaseModel
import PegSeparation.CFLNotPEG.Reduction.SCAFamilyCompiler


namespace PegSeparation.CFLNotPEG

open PegSeparation.Scaffolding
open PegSeparation.CellProbe


abbrev RecognizedByTotalPEG {Terminal : Type} [DecidableEq Terminal]
    (language : Language Terminal) : Prop :=
  PegSeparation.RecognizedByTotalPEG language

abbrev RecognizedBySCA {Terminal : Type}
    (language : Language Terminal) : Prop :=
  PegSeparation.RecognizedBySCA language

abbrev ConcreteAlphabet := PegSeparation.Witness.LanguageCFG.Terminal
abbrev ConcreteWord := PegSeparation.Witness.LanguageCFG.Word
abbrev ConcreteC : Language ConcreteAlphabet :=
  PegSeparation.Witness.LanguageCFG.C
abbrev WitnessLanguage : Language ConcreteAlphabet :=
  PegSeparation.Witness.LanguageCFG.L

theorem concreteC_isContextFree :
    Language.IsContextFree ConcreteC :=
  PegSeparation.Witness.LanguageCFG.Grammar.C_isContextFree

theorem witnessLanguage_isContextFree :
    Language.IsContextFree WitnessLanguage :=
  PegSeparation.Witness.LanguageCFG.Grammar.L_isContextFree

@[simp] theorem mem_witnessLanguage_iff (input : ConcreteWord) :
    input ∈ WitnessLanguage ↔ input.reverse ∈ ConcreteC :=
  Iff.rfl

theorem totalPEG_for_witness_implies_SCA_for_C
    (external : ExternalAssumptions) :
    RecognizedByTotalPEG WitnessLanguage → RecognizedBySCA ConcreteC := by
  rintro ⟨nonterminalCount, grammar, htotal, hrecognizes⟩
  obtain ⟨stateCount, workLabelCount, degree, radius, automaton, hautomaton⟩ :=
    external.loffForward grammar htotal
  refine ⟨stateCount, workLabelCount, degree, radius, automaton, ?_⟩
  intro input
  rw [hautomaton input, hrecognizes input.reverse]
  simp [WitnessLanguage, ConcreteC]

theorem witness_not_totalPEG_of_C_not_SCA
    (external : ExternalAssumptions)
    (hC : ¬ RecognizedBySCA ConcreteC) :
    ¬ RecognizedByTotalPEG WitnessLanguage := by
  intro hPEG
  exact hC (totalPEG_for_witness_implies_SCA_for_C external hPEG)


abbrev BitVector (n : ℕ) := PegSeparation.Witness.HardSlice.Vector n
abbrev IPMatrix (n : ℕ) := PegSeparation.Witness.HardSlice.Matrix n

def innerProductAnswer {n : ℕ} (S : IPMatrix n) (X : BitVector n)
    (query : Fin (PegSeparation.Witness.HardSlice.rowCount n)) : Bool :=
  PegSeparation.Reduction.MultiphaseModel.innerProductAnswer S X query

@[simp] theorem innerProductAnswer_eq_true_iff {n : ℕ}
    (S : IPMatrix n) (X : BitVector n)
    (query : Fin (PegSeparation.Witness.HardSlice.rowCount n)) :
    innerProductAnswer S X query = true ↔
      PegSeparation.Witness.HardSlice.vectorInnerProduct (S query) X = 1 := by
  exact
    PegSeparation.Reduction.MultiphaseModel.innerProductAnswer_eq_true_iff
      S X query

theorem hardWord_mem_C_iff_answer {n : ℕ}
    (S : IPMatrix n) (X : BitVector n)
    (query : Fin (PegSeparation.Witness.HardSlice.rowCount n)) :
    PegSeparation.Witness.HardSlice.hardWord S X query ∈ ConcreteC ↔
      innerProductAnswer S X query = true := by
  change
    PegSeparation.Witness.HardSlice.hardWord S X query ∈
        PegSeparation.Witness.LanguageCFG.C ↔
      innerProductAnswer S X query = true
  rw [PegSeparation.Witness.HardSlice.hardWord_mem_C_iff,
    innerProductAnswer_eq_true_iff]

def runUpdateList {n wordBits updateReads updateWrites : ℕ}
    (update : Fin n → Bool →
      PegSeparation.Reduction.SCAToCellProbe.UpdateProgram
        wordBits Unit updateReads updateWrites) :
    PegSeparation.Reduction.SCAToCellProbe.FiniteMemory wordBits →
      List (Fin n × Bool) →
      PegSeparation.Reduction.SCAToCellProbe.FiniteMemory wordBits
  := PegSeparation.Reduction.MultiphaseModel.runUpdateList update

def runAllUpdates {n wordBits updateReads updateWrites : ℕ}
    (update : Fin n → Bool →
      PegSeparation.Reduction.SCAToCellProbe.UpdateProgram
        wordBits Unit updateReads updateWrites)
    (memory : PegSeparation.Reduction.SCAToCellProbe.FiniteMemory wordBits)
    (X : BitVector n) :
    PegSeparation.Reduction.SCAToCellProbe.FiniteMemory wordBits :=
  PegSeparation.Reduction.MultiphaseModel.runAllUpdates update memory X

abbrev ExactMultiphaseIP
    (n wordBits updateReads updateWrites queryReads : ℕ) :=
  PegSeparation.Reduction.MultiphaseModel.ExactMultiphaseIP
    n wordBits updateReads updateWrites queryReads

def logScale (n : ℕ) : ℕ :=
  PegSeparation.Reduction.MultiphaseModel.logScale n

def scaledLogBudget (scale n : ℕ) : ℕ :=
  PegSeparation.Reduction.MultiphaseModel.scaledLogBudget scale n

abbrev HasFastMultiphaseIPFamily : Prop :=
  PegSeparation.Reduction.MultiphaseModel.HasFastMultiphaseIPFamily

abbrev SCAToDynamicCompilerStatement : Prop :=
  ∀ {stateCount workLabelCount degree radius : ℕ}
    (automaton : Scaffolding.Automaton ConcreteAlphabet
      stateCount workLabelCount degree radius),
    (∀ input, automaton.Accepts input ↔ input ∈ ConcreteC) →
      HasFastMultiphaseIPFamily

theorem scaToDynamicCompiler : SCAToDynamicCompilerStatement := by
  intro stateCount workLabelCount degree radius automaton decidesC
  exact
    PegSeparation.Reduction.SCAFamilyCompiler.fastMultiphaseIPFamily_of_SCA
      automaton decidesC

theorem fastMultiphaseIP_of_SCA :
    RecognizedBySCA ConcreteC → HasFastMultiphaseIPFamily := by
  rintro ⟨stateCount, workLabelCount, degree, radius, automaton, hautomaton⟩
  exact scaToDynamicCompiler automaton hautomaton


abbrev MultiphaseIPLowerBoundStatement : Prop :=
  ¬ HasFastMultiphaseIPFamily

theorem C_not_SCA_of_internal_pipeline
    (lowerBound : MultiphaseIPLowerBoundStatement) :
    ¬ RecognizedBySCA ConcreteC := by
  intro hSCA
  exact lowerBound (fastMultiphaseIP_of_SCA hSCA)

theorem final_separation_from_internal_pipeline
    (external : ExternalAssumptions)
    (lowerBound : MultiphaseIPLowerBoundStatement) :
    Language.IsContextFree WitnessLanguage ∧
      ¬ RecognizedByTotalPEG WitnessLanguage := by
  exact ⟨witnessLanguage_isContextFree,
    witness_not_totalPEG_of_C_not_SCA external
      (C_not_SCA_of_internal_pipeline lowerBound)⟩

theorem multiphaseIPLowerBound
    (external : ExternalAssumptions) :
    MultiphaseIPLowerBoundStatement := by
  exact external.ko2026MultiphaseIPLowerBound

theorem C_not_SCA (external : ExternalAssumptions) :
    ¬ RecognizedBySCA ConcreteC :=
  C_not_SCA_of_internal_pipeline (multiphaseIPLowerBound external)

theorem final_separation (external : ExternalAssumptions) :
    Language.IsContextFree WitnessLanguage ∧
      ¬ RecognizedByTotalPEG WitnessLanguage :=
  final_separation_from_internal_pipeline external
    (multiphaseIPLowerBound external)

end PegSeparation.CFLNotPEG
