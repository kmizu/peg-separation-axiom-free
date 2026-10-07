import PegSeparation.CFLNotPEG.Assembly
import PegSeparation.Closure.Factorization
import PegSeparation.Closure.ConcreteRegular
import PegSeparation.Closure.BooleanClosure
import PegSeparation.Closure.RegularToPEG
import PegSeparation.Closure.LeftRegularConcat
import PegSeparation.Closure.PrefixPEG
import PegSeparation.Closure.StarEquality


namespace PegSeparation.Closure

open Computability

theorem regularTail_isPEG :
    PegSeparation.RecognizedByTotalPEG RegularTail :=
  recognizedByTotalPEG_of_isRegular regularTail_isRegular

theorem starWitness_isPEG :
    PegSeparation.RecognizedByTotalPEG StarWitness := by
  unfold StarWitness
  exact recognizedByTotalPEG_union pref_isPEG
    (recognizedByTotalPEG_of_isRegular reversedRecord_isRegular)

theorem concatenation_nonclosure
    (external : PegSeparation.ExternalAssumptions) :
    PegSeparation.RecognizedByTotalPEG Pref ∧
      RegularTail.IsRegular ∧
      ¬ PegSeparation.RecognizedByTotalPEG (Pref * RegularTail) := by
  refine ⟨pref_isPEG, regularTail_isRegular, ?_⟩
  rw [← witness_factorization]
  exact (PegSeparation.CFLNotPEG.final_separation external).2

theorem concatenation_nonclosure_both_peg
    (external : PegSeparation.ExternalAssumptions) :
    PegSeparation.RecognizedByTotalPEG Pref ∧
      PegSeparation.RecognizedByTotalPEG RegularTail ∧
      ¬ PegSeparation.RecognizedByTotalPEG (Pref * RegularTail) :=
  ⟨pref_isPEG, regularTail_isPEG,
    (concatenation_nonclosure external).2.2⟩

theorem star_nonclosure
    (external : PegSeparation.ExternalAssumptions) :
    PegSeparation.RecognizedByTotalPEG StarWitness ∧
      ¬ PegSeparation.RecognizedByTotalPEG (StarWitness∗) := by
  refine ⟨starWitness_isPEG, ?_⟩
  intro hstar
  have hinter := recognizedByTotalPEG_inter hstar
    (recognizedByTotalPEG_of_isRegular shape_isRegular)
  rw [starWitness_kstar_inter_shape] at hinter
  exact (PegSeparation.CFLNotPEG.final_separation external).2 hinter

end PegSeparation.Closure
