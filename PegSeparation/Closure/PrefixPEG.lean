import PegSeparation.Closure.PrefixMachineCorrectness
import PegSeparation.Common.Compiler.RealTimeTM.Correctness
import PegSeparation.Common.Compiler.SCAToPEG.Final


namespace PegSeparation.Closure

open PegSeparation
open PegSeparation.Witness.LanguageCFG

theorem cFirst_compiledDegree :
    PegSeparation.RealTimeTM.CompiledDegree 2 = 6 := by
  decide

theorem cFirst_compiledSCA_accepts_iff (input : List Terminal) :
    (PegSeparation.RealTimeTM.toSCA prefixMachine).Accepts input ↔
      input ∈ CFirst := by
  exact
    (PegSeparation.RealTimeTM.toSCA_accepts_iff prefixMachine input).trans
      ((prefixMachine_accepts_iff_absRun input).trans
        (absRun_accept_iff input))

theorem cFirst_isSCA_degree_six_radius_two :
    ∃ (stateCount workLabelCount : ℕ)
      (automaton : PegSeparation.Scaffolding.Automaton
        Terminal stateCount workLabelCount 6 2),
      ∀ input, automaton.Accepts input ↔ input ∈ CFirst := by
  refine
    ⟨PegSeparation.RealTimeTM.CompiledStateCount 2 15 5,
      PegSeparation.RealTimeTM.CompiledLabelCount 2 5, ?_⟩
  rw [← cFirst_compiledDegree]
  exact
    ⟨PegSeparation.RealTimeTM.toSCA prefixMachine,
      cFirst_compiledSCA_accepts_iff⟩

theorem cFirst_isSCA : PegSeparation.RecognizedBySCA CFirst :=
  PegSeparation.RealTimeTM.recognizedBySCA_of_recognizedBy cFirst_recognizedBy

theorem pref_isPEG : PegSeparation.RecognizedByTotalPEG Pref := by
  obtain ⟨stateCount, workLabelCount, degree, radius, automaton, decides⟩ :=
    cFirst_isSCA
  obtain ⟨nonterminalCount, grammar, total, recognizes⟩ :=
    PegSeparation.SCAToPEG.loffBackward automaton
  refine ⟨nonterminalCount, grammar, total, ?_⟩
  intro input
  calc
    grammar.Recognizes input ↔ automaton.Accepts input.reverse := by
      simpa using (recognizes input.reverse).symm
    _ ↔ input.reverse ∈ CFirst := decides input.reverse
    _ ↔ input ∈ Pref := Iff.rfl

end PegSeparation.Closure
