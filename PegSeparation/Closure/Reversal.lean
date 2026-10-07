import PegSeparation.CFLNotPEG.Main
import PegSeparation.CFLNotPEG.Witness.DirectPEGPositive
import PegSeparation.CFLNotPEG.Witness.LinearLanguageCFG


namespace PegSeparation.Closure

open PegSeparation.Witness.LanguageCFG

theorem reverse_C_eq_L :
    Language.reverse (C : Language Terminal) = L :=
  rfl

theorem C_isPEG :
    PegSeparation.RecognizedByTotalPEG (C : Language Terminal) :=
  PegSeparation.Witness.DirectPEG.C_recognizedByTotalPEG

theorem C_not_SCA :
    ¬ PegSeparation.RecognizedBySCA (C : Language Terminal) :=
  PegSeparation.CFLNotPEG.C_not_SCA
    PegSeparation.CFLNotPEG.assumptions

theorem C_isLIN :
    Language.IsLinearContextFree (C : Language Terminal) :=
  LinearGrammar.C_isLinearContextFree

theorem reverse_C_isLIN :
    Language.IsLinearContextFree
      (Language.reverse (C : Language Terminal)) := by
  rw [reverse_C_eq_L]
  exact LinearGrammar.L_isLinearContextFree

theorem reverse_C_isSCA :
    PegSeparation.RecognizedBySCA
      (Language.reverse (C : Language Terminal)) := by
  obtain ⟨nonterminalCount, grammar, grammarTotal, grammarCorrect⟩ := C_isPEG
  obtain ⟨stateCount, workLabelCount, degree, radius, automaton,
      automatonCorrect⟩ :=
    PegSeparation.External.LoffForwardRepaired.loffForwardStatement
      grammar grammarTotal
  refine ⟨stateCount, workLabelCount, degree, radius, automaton, ?_⟩
  intro input
  exact (automatonCorrect input).trans (grammarCorrect input.reverse)

theorem reverse_C_not_PEG :
    ¬ PegSeparation.RecognizedByTotalPEG
      (Language.reverse (C : Language Terminal)) := by
  rw [reverse_C_eq_L]
  exact PegSeparation.CFLNotPEG.finalSeparation.2

theorem reversalNonClosure :
    PegSeparation.RecognizedByTotalPEG (C : Language Terminal) ∧
      ¬ PegSeparation.RecognizedByTotalPEG
        (Language.reverse (C : Language Terminal)) :=
  ⟨C_isPEG, reverse_C_not_PEG⟩

theorem orientationSeparation :
    (PegSeparation.RecognizedByTotalPEG (C : Language Terminal) ∧
      ¬ PegSeparation.RecognizedBySCA (C : Language Terminal)) ∧
    (PegSeparation.RecognizedBySCA
        (Language.reverse (C : Language Terminal)) ∧
      ¬ PegSeparation.RecognizedByTotalPEG
        (Language.reverse (C : Language Terminal))) :=
  ⟨⟨C_isPEG, C_not_SCA⟩, ⟨reverse_C_isSCA, reverse_C_not_PEG⟩⟩

theorem linearOrientationSeparation :
    (Language.IsLinearContextFree (C : Language Terminal) ∧
      PegSeparation.RecognizedByTotalPEG (C : Language Terminal) ∧
      ¬ PegSeparation.RecognizedBySCA (C : Language Terminal)) ∧
    (Language.IsLinearContextFree
        (Language.reverse (C : Language Terminal)) ∧
      PegSeparation.RecognizedBySCA
        (Language.reverse (C : Language Terminal)) ∧
      ¬ PegSeparation.RecognizedByTotalPEG
        (Language.reverse (C : Language Terminal))) :=
  ⟨⟨C_isLIN, C_isPEG, C_not_SCA⟩,
    ⟨reverse_C_isLIN, reverse_C_isSCA, reverse_C_not_PEG⟩⟩

end PegSeparation.Closure
