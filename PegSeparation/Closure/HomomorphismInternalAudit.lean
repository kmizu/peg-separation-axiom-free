import PegSeparation.Closure.HomomorphismInternal
import PegSeparation.CFLNotPEG.Main

set_option linter.style.header false


namespace PegSeparation.Closure.HomomorphismInternal

theorem homomorphismNonClosureInternal :
    ∃ (language :
          Language
            (Option
              PegSeparation.Witness.LanguageCFG.Terminal))
        (hom :
          WordHom
            (Option
              PegSeparation.Witness.LanguageCFG.Terminal)
            PegSeparation.Witness.LanguageCFG.Terminal),
      PegSeparation.RecognizedByTotalPEG language ∧
        ¬ PegSeparation.RecognizedByTotalPEG
          (wordHomImage hom language) :=
  homomorphism_nonclosure_internal
    PegSeparation.CFLNotPEG.assumptions

theorem substitutionNonClosureInternal :
    ∃ (language :
          Language
            (Option
              PegSeparation.Witness.LanguageCFG.Terminal))
        (substitution :
          Substitution
            (Option
              PegSeparation.Witness.LanguageCFG.Terminal)
            PegSeparation.Witness.LanguageCFG.Terminal),
      PegSeparation.RecognizedByTotalPEG language ∧
        (∀ symbol,
          PegSeparation.RecognizedByTotalPEG
            (substitution symbol)) ∧
          ¬ PegSeparation.RecognizedByTotalPEG
            (substitutionImage substitution language) :=
  substitution_nonclosure_internal
    PegSeparation.CFLNotPEG.assumptions

#check markedConcatenationWitness_isPEG
#check markedConcatenationWitness_erases
#check homomorphismNonClosureInternal
#check substitutionNonClosureInternal

#print axioms liftGrammar_isLoffTotal
#print axioms recognizedByTotalPEG_markedProduct
#print axioms markedConcatenationWitness_isPEG
#print axioms markedConcatenationWitness_erases
#print axioms eraseSingletonSubstitution_components_arePEG
#print axioms homomorphismNonClosureInternal
#print axioms substitutionNonClosureInternal

end PegSeparation.Closure.HomomorphismInternal
