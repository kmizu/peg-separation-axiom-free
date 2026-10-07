import PegSeparation.Common.Recognition


namespace PegSeparation.SCAToPEG

open PegSeparation

abbrev LoffBackwardStatement : Prop :=
  ∀ {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    {stateCount workLabelCount degree radius : Nat}
    (automaton : Scaffolding.Automaton Terminal
      stateCount workLabelCount degree radius),
    ∃ (nonterminalCount : Nat)
      (grammar : PegGrammar Terminal nonterminalCount),
      grammar.IsLoffTotal ∧
        ∀ input,
          automaton.Accepts input ↔ grammar.Recognizes input.reverse

end PegSeparation.SCAToPEG
