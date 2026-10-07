import PegSeparation.CFLNotPEG.External.Loff.Construction
import PegSeparation.CFLNotPEG.External.Statements


namespace PegSeparation.External.LoffForwardRepaired

open PegSeparation

theorem loffForwardStatement : LoffForwardStatement := by
  intro Terminal terminalFintype terminalDecidable nonterminalCount grammar total
  exact ⟨2,
    Construction.WorkLabelCount grammar,
    Construction.Degree grammar,
    Construction.Radius grammar,
    Construction.automaton grammar total,
    Construction.automaton_accepts_iff grammar total⟩

end PegSeparation.External.LoffForwardRepaired
