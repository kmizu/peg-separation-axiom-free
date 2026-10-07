import PegSeparation.CFLNotPEG.Reduction.SCAToCellProbe


namespace PegSeparation.Reduction.ThreeStageModel

open PegSeparation.Reduction.SCAToCellProbe

structure Problem where
  Data : ℕ → Type
  Update : ℕ → Type
  Query : ℕ → Type
  updateCount : ℕ → ℕ
  updateCount_pos : ∀ n, 0 < updateCount n
  answer : ∀ n, Data n → (Fin (updateCount n) → Update n) → Query n → Bool

def encodedUpdates {Terminal : Type} (problem : Problem)
    (update : ∀ n, Fin (problem.updateCount n) →
      problem.Update n → List Terminal)
    (n : ℕ) (updates : Fin (problem.updateCount n) → problem.Update n) :
    List Terminal :=
  (List.ofFn fun index => update n index (updates index)).flatten

def encodedWord {Terminal : Type} (problem : Problem)
    (pre : ∀ n, problem.Data n → List Terminal)
    (update : ∀ n, Fin (problem.updateCount n) →
      problem.Update n → List Terminal)
    (query : ∀ n, problem.Query n → List Terminal)
    (n : ℕ) (data : problem.Data n)
    (updates : Fin (problem.updateCount n) → problem.Update n)
    (finalQuery : problem.Query n) : List Terminal :=
  pre n data ++ encodedUpdates problem update n updates ++ query n finalQuery

structure Encoding (Terminal : Type) (problem : Problem) where
  language : List Terminal → Prop
  updateBound : ℕ → ℕ
  queryBound : ℕ → ℕ
  updateBound_pos : ∀ n, 0 < updateBound n
  queryBound_pos : ∀ n, 0 < queryBound n
  pre : ∀ n, problem.Data n → List Terminal
  update : ∀ n, Fin (problem.updateCount n) →
    problem.Update n → List Terminal
  query : ∀ n, problem.Query n → List Terminal
  correct : ∀ n data updates finalQuery,
    language
      (encodedWord problem pre update query n data updates finalQuery) ↔
      problem.answer n data updates finalQuery = true
  update_length : ∀ n index value,
    (update n index value).length ≤ updateBound n
  query_length : ∀ n value, (query n value).length ≤ queryBound n
  polynomialConstant : ℕ
  polynomialExponent : ℕ
  polynomialConstant_pos : 0 < polynomialConstant
  total_length : ∀ n data updates finalQuery,
    (encodedWord problem pre update query n data updates finalQuery).length ≤
      polynomialConstant * (n + 1) ^ polynomialExponent

namespace Encoding

variable {Terminal : Type} {problem : Problem}

def updateWord (encoding : Encoding Terminal problem) (n : ℕ)
    (updates : Fin (problem.updateCount n) → problem.Update n) :
    List Terminal :=
  encodedUpdates problem encoding.update n updates

def word (encoding : Encoding Terminal problem) (n : ℕ)
    (data : problem.Data n)
    (updates : Fin (problem.updateCount n) → problem.Update n)
    (finalQuery : problem.Query n) : List Terminal :=
  encodedWord problem encoding.pre encoding.update encoding.query
    n data updates finalQuery

end Encoding

structure BoundedUpdate (wordBits readBound writeBound : ℕ) where
  reads : ℕ
  writes : ℕ
  program : UpdateProgram wordBits Unit reads writes
  reads_le : reads ≤ readBound
  writes_le : writes ≤ writeBound

structure BoundedQuery (wordBits readBound : ℕ) where
  reads : ℕ
  program : ReadProgram wordBits Bool reads
  reads_le : reads ≤ readBound

namespace BoundedUpdate

def execute {wordBits readBound writeBound : ℕ}
    (operation : BoundedUpdate wordBits readBound writeBound)
    (memory : FiniteMemory wordBits) : FiniteMemory wordBits :=
  (operation.program.execute memory).memory

end BoundedUpdate

namespace BoundedQuery

def execute {wordBits readBound : ℕ}
    (operation : BoundedQuery wordBits readBound)
    (memory : FiniteMemory wordBits) : Bool :=
  (operation.program.execute memory).result

end BoundedQuery

def runUpdateList {Update : Type} {count wordBits readBound writeBound : ℕ}
    (operation : Fin count → Update →
      BoundedUpdate wordBits readBound writeBound) :
    FiniteMemory wordBits → List (Fin count × Update) →
      FiniteMemory wordBits
  | memory, [] => memory
  | memory, invocation :: rest =>
      runUpdateList operation
        ((operation invocation.1 invocation.2).execute memory) rest

def runUpdates {Update : Type} {count wordBits readBound writeBound : ℕ}
    (operation : Fin count → Update →
      BoundedUpdate wordBits readBound writeBound)
    (memory : FiniteMemory wordBits) (updates : Fin count → Update) :
    FiniteMemory wordBits :=
  runUpdateList operation memory
    (List.ofFn fun index => (index, updates index))

structure ExactStructure (problem : Problem) (n wordBits maxUpdateReads
    maxUpdateWrites maxQueryReads : ℕ) where
  preprocess : problem.Data n → FiniteMemory wordBits
  update : Fin (problem.updateCount n) → problem.Update n →
    BoundedUpdate wordBits maxUpdateReads maxUpdateWrites
  query : problem.Query n → BoundedQuery wordBits maxQueryReads
  correct : ∀ data updates finalQuery,
    (query finalQuery).execute
      (runUpdates update (preprocess data) updates) =
        problem.answer n data updates finalQuery

end PegSeparation.Reduction.ThreeStageModel
