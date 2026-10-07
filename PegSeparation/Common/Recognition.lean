import PegSeparation.Common.Model.PEG
import PegSeparation.Common.Model.Scaffolding


namespace PegSeparation

def RecognizedByTotalPEG {Terminal : Type} [DecidableEq Terminal]
    (language : Language Terminal) : Prop :=
  ∃ (nonterminalCount : ℕ)
    (grammar : PegGrammar Terminal nonterminalCount),
      grammar.IsLoffTotal ∧
        ∀ input, grammar.Recognizes input ↔ input ∈ language

def RecognizedBySCA {Terminal : Type} (language : Language Terminal) : Prop :=
  ∃ (stateCount workLabelCount degree radius : ℕ)
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius),
      ∀ input, automaton.Accepts input ↔ input ∈ language

end PegSeparation
