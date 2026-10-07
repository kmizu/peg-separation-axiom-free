import PegSeparation.Common.Compiler.SCAToPEG.StateLabel
import PegSeparation.Common.Compiler.SCAToPEG.PathEvaluation
import PegSeparation.Common.Compiler.SCAToPEG.TerminalAccept
import PegSeparation.Common.Compiler.SCAToPEG.FinalSupport


namespace PegSeparation.SCAToPEG

open PegSeparation
open PegSeparation.Scaffolding

noncomputable section

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
variable {stateCount workLabelCount degree radius : Nat}

theorem evaluates_name
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (name : Name stateCount workLabelCount degree radius)
    (input : List Terminal) :
    (grammar automaton).Evaluates (invoke name) input
      (nameResult automaton name input) := by
  let metric :
      Name stateCount workLabelCount degree radius × List Terminal → Nat :=
    fun pair => nameMeasure pair.1 pair.2
  refine (measure metric).wf.induction
    (C := fun pair =>
      (grammar automaton).Evaluates (invoke pair.1) pair.2
        (nameResult automaton pair.1 pair.2))
    (name, input) ?_
  rintro ⟨current, currentInput⟩ inductionHypothesis
  have recurse : ∀
      (childName : Name stateCount workLabelCount degree radius)
      (childInput : List Terminal),
      nameMeasure childName childInput <
          nameMeasure current currentInput →
      (grammar automaton).Evaluates (invoke childName) childInput
        (nameResult automaton childName childInput) := by
    intro childName childInput smaller
    exact inductionHypothesis (childName, childInput) smaller
  apply PegGrammar.Evaluates.nonterminal
  rw [grammar_rule_encode]
  cases current with
  | state wanted =>
      simpa [ruleFor] using
        evaluates_stateRule automaton wanted currentInput recurse
  | label wanted =>
      simpa [ruleFor] using
        evaluates_labelRule automaton wanted currentInput recurse
  | hood expected =>
      simpa [ruleFor, nameResult] using
        evaluates_hoodRule automaton expected currentInput recurse
  | path path =>
      simpa [ruleFor, nameResult] using
        evaluates_pathRule automaton path currentInput recurse
  | consumeAll =>
      simpa [ruleFor] using
        evaluates_consumeAllRule automaton currentInput recurse
  | accepts =>
      simpa [ruleFor] using
        evaluates_acceptsRule automaton currentInput recurse

theorem grammar_isLoffTotal
    (automaton : Automaton Terminal stateCount workLabelCount degree radius) :
    (grammar automaton).IsLoffTotal :=
  grammar_isLoffTotal_of_evaluates_name automaton (evaluates_name automaton)

theorem automaton_accepts_iff
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) :
    automaton.Accepts input ↔ (grammar automaton).Recognizes input.reverse :=
  automaton_accepts_iff_recognizes_of_evaluates_name automaton
    (evaluates_name automaton) input

theorem loffBackwardStatement : PegSeparation.SCAToPEG.LoffBackwardStatement := by
  intro Terminal terminalFintype terminalDecidable
    stateCount workLabelCount degree radius automaton
  exact ⟨NameCount stateCount workLabelCount degree radius,
    grammar automaton, grammar_isLoffTotal automaton,
    automaton_accepts_iff automaton⟩

end

end PegSeparation.SCAToPEG

namespace PegSeparation.SCAToPEG

theorem loffBackward : LoffBackwardStatement :=
  PegSeparation.SCAToPEG.loffBackwardStatement

end PegSeparation.SCAToPEG
