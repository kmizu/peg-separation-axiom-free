import PegSeparation.CFLNotPEG.Witness.DirectPEGCorrectness
import PegSeparation.Common.Recognition


namespace PegSeparation.Witness.DirectPEG

open PegSeparation

theorem C_recognizedByTotalPEG :
    PegSeparation.RecognizedByTotalPEG
      (LanguageCFG.C : Language Terminal) :=
  ⟨10, grammar, grammar_isLoffTotal, grammar_recognizes_iff_C⟩

end PegSeparation.Witness.DirectPEG
