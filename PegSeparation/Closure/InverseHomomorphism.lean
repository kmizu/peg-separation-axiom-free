import PegSeparation.External.BirmanUllman1973


namespace PegSeparation.Closure

theorem recognizedByTotalPEG_inverseImage
    {Source Target : Type}
    [Finite Source] [DecidableEq Source]
    [Finite Target] [DecidableEq Target]
    (hom : WordHom Source Target)
    {language : Language Target}
    (recognized : PegSeparation.RecognizedByTotalPEG language) :
    PegSeparation.RecognizedByTotalPEG (hom.inverseImage language) :=
  PegSeparation.External.BirmanUllman1973.recognizedByTotalPEG_inverseImage
    hom recognized

end PegSeparation.Closure

#check PegSeparation.Closure.recognizedByTotalPEG_inverseImage
#print axioms PegSeparation.Closure.recognizedByTotalPEG_inverseImage
