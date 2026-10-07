import PegSeparation.CFLNotPEG.Model.CellProbe


open scoped BigOperators

namespace PegSeparation

structure FiniteDistribution (Outcome : Type) [Fintype Outcome] where
  mass : Outcome → ℝ
  mass_nonnegative : ∀ outcome, 0 ≤ mass outcome
  mass_sum : ∑ outcome, mass outcome = 1

structure BinaryProblem (Input Query : Type) where
  value : Query → Input → Bool

namespace BinaryProblem

variable {Input Query : Type}

def character (problem : BinaryProblem Input Query) (query : Query) (input : Input) : ℝ :=
  if problem.value query input then -1 else 1

variable [Fintype Input]

def IsBalanced (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input) : Prop :=
  ∀ query, ∑ input, inputDistribution.mass input * problem.character query input = 0

end BinaryProblem

structure PublicCoinProtocol (Input : Type) (messageBits coinCount : Nat) where
  coinDistribution : FiniteDistribution (Fin coinCount)
  encode : Fin coinCount → Input → BitVec messageBits

namespace PublicCoinProtocol

variable {Input Query : Type} [Fintype Input] [Fintype Query]
  {messageBits coinCount : Nat}

noncomputable def advantage (protocol : PublicCoinProtocol Input messageBits coinCount)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) : ℝ :=
  ∑ coin, protocol.coinDistribution.mass coin *
    ∑ query, queryDistribution.mass query *
      ∑ message : BitVec messageBits,
        |∑ input, inputDistribution.mass input *
          (if protocol.encode coin input = message then problem.character query input else 0)|

end PublicCoinProtocol

namespace CellProbe.StaticStructure

variable {Input Query : Type} [Fintype Input] [Fintype Query]
  {wordBits cacheCells maxUpdatedCells : Nat}

def Solves (dataStructure : CellProbe.StaticStructure Input Query
    wordBits cacheCells maxUpdatedCells) (problem : BinaryProblem Input Query) : Prop :=
  ∀ input query, dataStructure.answer input query = problem.value query input

noncomputable def expectedTotalProbes
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) : ℝ :=
  ∑ input, inputDistribution.mass input *
    ∑ query, queryDistribution.mass query *
      (dataStructure.probeTrace input query).length

noncomputable def expectedUpdatedProbes
    (dataStructure : CellProbe.StaticStructure Input Query
      wordBits cacheCells maxUpdatedCells)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) : ℝ :=
  ∑ input, inputDistribution.mass input *
    ∑ query, queryDistribution.mass query * dataStructure.updatedProbeCount input query

end CellProbe.StaticStructure

noncomputable def log₂ (x : ℝ) : ℝ := Real.log x / Real.log 2

end PegSeparation
