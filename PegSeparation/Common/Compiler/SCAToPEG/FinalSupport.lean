import PegSeparation.Common.Compiler.SCAToPEG.CompilerCorrectness


namespace PegSeparation.SCAToPEG

open PegSeparation
open PegSeparation.Scaffolding

noncomputable section

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
variable {stateCount workLabelCount degree radius : Nat}

theorem grammar_isLoffTotal_of_evaluates_name
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (allNames : ∀
      (name : Name stateCount workLabelCount degree radius)
      (input : List Terminal),
      (grammar automaton).Evaluates (invoke name) input
        (nameResult automaton name input)) :
    (grammar automaton).IsLoffTotal := by
  apply PegGrammar.isLoffTotal_of_nonterminal_total
  intro encoded input
  let name := decodeName encoded
  refine ⟨nameResult automaton name input, ?_⟩
  have evaluated := allNames name input
  simpa [invoke, name] using evaluated

theorem automaton_accepts_iff_recognizes_of_evaluates_name
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (allNames : ∀
      (name : Name stateCount workLabelCount degree radius)
      (input : List Terminal),
      (grammar automaton).Evaluates (invoke name) input
        (nameResult automaton name input))
    (input : List Terminal) :
    automaton.Accepts input ↔ (grammar automaton).Recognizes input.reverse := by
  constructor
  · intro accepted
    have accepted' : (automaton.run input).1 ∈ automaton.accepting := by
      simpa [Automaton.Accepts] using accepted
    have evaluated := allNames
      (.accepts : Name stateCount workLabelCount degree radius) input.reverse
    have succeeds : (grammar automaton).Evaluates
        (invoke (.accepts : Name stateCount workLabelCount degree radius))
        input.reverse (.success []) := by
      simpa [nameResult, reverseConfig, accepted'] using evaluated
    simpa [PegGrammar.Recognizes, invoke] using succeeds
  · intro recognized
    have recognized' : (grammar automaton).Evaluates
        (invoke (.accepts : Name stateCount workLabelCount degree radius))
        input.reverse (.success []) := by
      simpa [PegGrammar.Recognizes, invoke] using recognized
    by_contra rejected
    have rejected' : (automaton.run input).1 ∉ automaton.accepting := by
      simpa [Automaton.Accepts] using rejected
    have evaluated := allNames
      (.accepts : Name stateCount workLabelCount degree radius) input.reverse
    have fails : (grammar automaton).Evaluates
        (invoke (.accepts : Name stateCount workLabelCount degree radius))
        input.reverse .failure := by
      simpa [nameResult, reverseConfig, rejected'] using evaluated
    have impossible :=
      PegSeparation.External.LoffForwardRepaired.PegGrammar.evaluates_deterministic
        recognized' fails
    cases impossible

end

end PegSeparation.SCAToPEG
