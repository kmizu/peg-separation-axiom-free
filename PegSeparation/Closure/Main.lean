import PegSeparation.Closure.Assembly
import PegSeparation.Closure.ComplementClosure
import PegSeparation.Closure.GreibachHardest
import PegSeparation.Closure.HomomorphismInternalAudit
import PegSeparation.Closure.InverseHomomorphism
import PegSeparation.Closure.KleenePlus
import PegSeparation.Closure.Reversal
import PegSeparation.CFLNotPEG.Main

set_option linter.style.header false


namespace PegSeparation.Closure

open Computability

theorem concatenationNonClosure :
    PegSeparation.RecognizedByTotalPEG Pref ∧
      RegularTail.IsRegular ∧
      ¬ PegSeparation.RecognizedByTotalPEG (Pref * RegularTail) :=
  concatenation_nonclosure PegSeparation.CFLNotPEG.assumptions

theorem concatenationNonClosureBothPEG :
    PegSeparation.RecognizedByTotalPEG Pref ∧
      PegSeparation.RecognizedByTotalPEG RegularTail ∧
      ¬ PegSeparation.RecognizedByTotalPEG (Pref * RegularTail) :=
  concatenation_nonclosure_both_peg PegSeparation.CFLNotPEG.assumptions

theorem kleeneStarNonClosure :
    PegSeparation.RecognizedByTotalPEG StarWitness ∧
      ¬ PegSeparation.RecognizedByTotalPEG (StarWitness∗) :=
  star_nonclosure PegSeparation.CFLNotPEG.assumptions

theorem kleenePlusNonClosure :
    PegSeparation.RecognizedByTotalPEG StarWitness ∧
      ¬ PegSeparation.RecognizedByTotalPEG
        (kleenePlus StarWitness) :=
  kleenePlus_nonclosure PegSeparation.CFLNotPEG.assumptions

end PegSeparation.Closure

#check PegSeparation.Closure.concatenationNonClosure
#check PegSeparation.Closure.kleeneStarNonClosure
#check PegSeparation.Closure.kleenePlusNonClosure
#check PegSeparation.Closure.reversalNonClosure
#check PegSeparation.Closure.linearOrientationSeparation
#check PegSeparation.Closure.HomomorphismInternal.homomorphismNonClosureInternal
#check PegSeparation.Closure.HomomorphismInternal.substitutionNonClosureInternal
#check PegSeparation.Closure.GreibachHardest.greibachHardest_isContextFree_not_totalPEG


#print axioms PegSeparation.Closure.witness_factorization
#print axioms PegSeparation.Witness.LanguageCFG.LinearGrammar.nonterminal_card
#print axioms PegSeparation.Witness.LanguageCFG.LinearGrammar.alternative_card
#print axioms PegSeparation.Witness.LanguageCFG.LinearGrammar.cfg_isLinear
#print axioms PegSeparation.Witness.LanguageCFG.LinearGrammar.cfg_language_eq_C
#print axioms PegSeparation.Witness.LanguageCFG.LinearGrammar.C_isLinearContextFree
#print axioms PegSeparation.Witness.LanguageCFG.LinearGrammar.L_isLinearContextFree
#print axioms PegSeparation.Closure.cFirst_compiledDegree
#print axioms PegSeparation.Closure.cFirst_isSCA_degree_six_radius_two
#print axioms PegSeparation.Closure.pref_isPEG
#print axioms PegSeparation.Closure.regularTail_isRegular
#print axioms PegSeparation.Closure.reversedRecord_isRegular
#print axioms PegSeparation.Closure.shape_isRegular
#print axioms PegSeparation.Closure.recognizedByTotalPEG_union
#print axioms PegSeparation.Closure.recognizedByTotalPEG_inter
#print axioms PegSeparation.Closure.recognizedByTotalPEG_compl
#print axioms PegSeparation.Closure.recognizedByTotalPEG_of_isRegular
#print axioms PegSeparation.Closure.recognizedByTotalPEG_mul_of_isRegular_left
#print axioms PegSeparation.Closure.starWitness_isPEG
#print axioms PegSeparation.Closure.starWitness_kstar_inter_shape
#print axioms PegSeparation.Closure.epsilonLanguage_isPEG
#print axioms PegSeparation.Closure.HomomorphismInternal.recognizedByTotalPEG_markedProduct
#print axioms PegSeparation.Closure.HomomorphismInternal.markedConcatenationWitness_isPEG
#print axioms PegSeparation.Closure.HomomorphismInternal.markedConcatenationWitness_erases
#print axioms PegSeparation.Closure.C_isPEG
#print axioms PegSeparation.Closure.C_isLIN
#print axioms PegSeparation.Closure.reverse_C_isLIN
#print axioms PegSeparation.Closure.reverse_C_isSCA


#print axioms PegSeparation.Closure.recognizedByTotalPEG_inverseImage


#print axioms PegSeparation.Closure.concatenationNonClosure
#print axioms PegSeparation.Closure.concatenationNonClosureBothPEG
#print axioms PegSeparation.Closure.kleeneStarNonClosure
#print axioms PegSeparation.Closure.kleenePlusNonClosure
#print axioms PegSeparation.Closure.reversalNonClosure
#print axioms PegSeparation.Closure.linearOrientationSeparation
#print axioms PegSeparation.Closure.HomomorphismInternal.homomorphismNonClosureInternal
#print axioms PegSeparation.Closure.HomomorphismInternal.substitutionNonClosureInternal


#print axioms PegSeparation.Closure.GreibachHardest.greibachHardest_isContextFree_not_totalPEG
