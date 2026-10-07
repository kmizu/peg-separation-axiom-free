import PegSeparation.Closure.WordHom


namespace PegSeparation.External.BirmanUllman1973

open PegSeparation.Closure

axiom recognizedByTotalPEG_inverseImage
    {Source Target : Type}
    [Finite Source] [DecidableEq Source]
    [Finite Target] [DecidableEq Target]
    (hom : WordHom Source Target)
    {language : Language Target}
    (recognized : PegSeparation.RecognizedByTotalPEG language) :
    PegSeparation.RecognizedByTotalPEG (hom.inverseImage language)

end PegSeparation.External.BirmanUllman1973
