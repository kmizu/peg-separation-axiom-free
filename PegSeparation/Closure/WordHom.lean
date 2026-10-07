import PegSeparation.Common.Recognition


namespace PegSeparation.Closure

universe u v

@[ext]
structure WordHom (Source : Type u) (Target : Type v) where
  letterImage : Source → List Target

namespace WordHom

variable {Source : Type u} {Target : Type v}

def extend (hom : WordHom Source Target) (word : List Source) : List Target :=
  word.flatMap hom.letterImage

@[simp] theorem extend_nil (hom : WordHom Source Target) :
    hom.extend [] = [] :=
  rfl

@[simp] theorem extend_cons (hom : WordHom Source Target)
    (letter : Source) (word : List Source) :
    hom.extend (letter :: word) =
      hom.letterImage letter ++ hom.extend word := by
  simp [extend]

@[simp] theorem extend_append (hom : WordHom Source Target)
    (left right : List Source) :
    hom.extend (left ++ right) = hom.extend left ++ hom.extend right := by
  simp [extend]

def inverseImage (hom : WordHom Source Target)
    (language : Language Target) : Language Source :=
  fun word => hom.extend word ∈ language

@[simp] theorem mem_inverseImage_iff (hom : WordHom Source Target)
    (language : Language Target) (word : List Source) :
    word ∈ hom.inverseImage language ↔ hom.extend word ∈ language :=
  Iff.rfl

end WordHom

end PegSeparation.Closure
