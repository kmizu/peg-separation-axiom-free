import Mathlib


namespace PegSeparation

namespace CellProbe

abbrev Address (wordBits : Nat) := BitVec wordBits
abbrev Word (wordBits : Nat) := BitVec wordBits

inductive QueryTree (wordBits : Nat) where
  | answer (value : Bool)
  | probe (address : Address wordBits) (next : Word wordBits → QueryTree wordBits)

namespace QueryTree

variable {wordBits : Nat}

def run (memory : Address wordBits → Word wordBits) :
    QueryTree wordBits → Bool × List (Address wordBits)
  | .answer value => (value, [])
  | .probe address next =>
      let continuation := run memory (next (memory address))
      (continuation.1, address :: continuation.2)

end QueryTree

structure StaticStructure (Input Query : Type)
    (wordBits cacheCells maxUpdatedCells : Nat) where
  preMemory : Address wordBits → Word wordBits
  updatedAddresses : Input → Finset (Address wordBits)
  updatedWord : Input → Address wordBits → Word wordBits
  updateBound : ∀ input, (updatedAddresses input).card ≤ maxUpdatedCells
  cache : Input → Fin cacheCells → Word wordBits
  queryAlgorithm : Query → (Fin cacheCells → Word wordBits) → QueryTree wordBits

namespace StaticStructure

variable {Input Query : Type} {wordBits cacheCells maxUpdatedCells : Nat}

def memory (dataStructure : StaticStructure Input Query wordBits cacheCells maxUpdatedCells)
    (input : Input) (address : Address wordBits) : Word wordBits :=
  if address ∈ dataStructure.updatedAddresses input then
    dataStructure.updatedWord input address
  else
    dataStructure.preMemory address

def execute (dataStructure : StaticStructure Input Query wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query) : Bool × List (Address wordBits) :=
  (dataStructure.queryAlgorithm query (dataStructure.cache input)).run
    (dataStructure.memory input)

def answer (dataStructure : StaticStructure Input Query wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query) : Bool :=
  (dataStructure.execute input query).1

def probeTrace (dataStructure : StaticStructure Input Query wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query) : List (Address wordBits) :=
  (dataStructure.execute input query).2

def updatedProbeCount
    (dataStructure : StaticStructure Input Query wordBits cacheCells maxUpdatedCells)
    (input : Input) (query : Query) : Nat :=
  (dataStructure.probeTrace input query).countP (fun address =>
    address ∈ dataStructure.updatedAddresses input)

end StaticStructure

end CellProbe

end PegSeparation
