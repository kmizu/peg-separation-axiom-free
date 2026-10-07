import PegSeparation.Common.Compiler.SCAToPEG.Final


namespace PegSeparation.Closure

open PegSeparation

section SCAOfDFA

variable {Terminal : Type} {StateType : Type} [Fintype StateType]

private noncomputable def stateIndex (StateType : Type) [Fintype StateType] :
    StateType ≃ Fin (Fintype.card StateType) :=
  Fintype.equivFin StateType

private noncomputable def scaOfDFA (machine : DFA Terminal StateType) :
    Scaffolding.Automaton Terminal (Fintype.card StateType) 1 1 0 :=
  letI : DecidablePred fun index : Fin (Fintype.card StateType) =>
      (stateIndex StateType).symm index ∈ machine.accept := fun _ => Classical.dec _
  { degreePositive := Nat.one_pos
    initialState := stateIndex StateType machine.start
    accepting :=
      Finset.univ.filter fun index => (stateIndex StateType).symm index ∈ machine.accept
    transition := fun state symbol _ =>
      { nextState :=
          stateIndex StateType (machine.step ((stateIndex StateType).symm state) symbol)
        newLabel := 0
        target := fun _ => .missing } }

private theorem scaOfDFA_foldl_fst (machine : DFA Terminal StateType)
    (input : List Terminal)
    (configuration :
      Fin (Fintype.card StateType) ×
        Scaffolding.Scaffold (Fin 1) 1) :
    (input.foldl (scaOfDFA machine).step configuration).1 =
      stateIndex StateType
        (machine.evalFrom ((stateIndex StateType).symm configuration.1) input) := by
  induction input generalizing configuration with
  | nil => simp
  | cons symbol rest ih =>
      rw [List.foldl_cons, ih]
      simp [Scaffolding.Automaton.step, scaOfDFA]

private theorem scaOfDFA_run_fst (machine : DFA Terminal StateType)
    (input : List Terminal) :
    ((scaOfDFA machine).run input).1 = stateIndex StateType (machine.eval input) := by
  rw [Scaffolding.Automaton.run, scaOfDFA_foldl_fst]
  simp [scaOfDFA, DFA.eval]

private theorem scaOfDFA_accepts_iff (machine : DFA Terminal StateType)
    (input : List Terminal) :
    (scaOfDFA machine).Accepts input ↔ input ∈ machine.accepts := by
  letI : DecidablePred fun index : Fin (Fintype.card StateType) =>
      (stateIndex StateType).symm index ∈ machine.accept := fun _ => Classical.dec _
  rw [Scaffolding.Automaton.Accepts, scaOfDFA_run_fst]
  simp [scaOfDFA, DFA.mem_accepts]

end SCAOfDFA

theorem recognizedBySCA_of_isRegular {Terminal : Type} {L : Language Terminal}
    (h : L.IsRegular) : PegSeparation.RecognizedBySCA L := by
  obtain ⟨StateType, stateFintype, machine, hmachine⟩ := h
  exact ⟨Fintype.card StateType, 1, 1, 0, scaOfDFA machine,
    fun input => by rw [scaOfDFA_accepts_iff, hmachine]⟩

theorem recognizedByTotalPEG_of_accepts {Terminal : Type} [Fintype Terminal]
    [DecidableEq Terminal] {L : Language Terminal}
    (hsca : PegSeparation.RecognizedBySCA (Language.reverse L)) :
    PegSeparation.RecognizedByTotalPEG L := by
  obtain ⟨stateCount, workLabelCount, degree, radius, automaton, hautomaton⟩ := hsca
  obtain ⟨nonterminalCount, grammar, htotal, hgrammar⟩ :=
    PegSeparation.SCAToPEG.loffBackward automaton
  refine ⟨nonterminalCount, grammar, htotal, fun input => ?_⟩
  have hstep := (hgrammar input.reverse).symm.trans (hautomaton input.reverse)
  rw [List.reverse_reverse] at hstep
  exact hstep.trans Language.reverse_mem_reverse

theorem recognizedByTotalPEG_of_isRegular {Terminal : Type} [Fintype Terminal]
    [DecidableEq Terminal] {L : Language Terminal} (h : L.IsRegular) :
    PegSeparation.RecognizedByTotalPEG L :=
  recognizedByTotalPEG_of_accepts (recognizedBySCA_of_isRegular h.reverse)

end PegSeparation.Closure
