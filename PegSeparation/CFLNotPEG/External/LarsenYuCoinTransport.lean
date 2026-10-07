import PegSeparation.CFLNotPEG.External.LarsenYuBernoulli
import PegSeparation.CFLNotPEG.External.LarsenYuFiniteMessageEmbedding


open scoped BigOperators

namespace PegSeparation.External.LarsenYuCoinTransport

noncomputable section

open LarsenYuBernoulli LarsenYuFiniteMessageEmbedding

def outcomeStructuredAdvantage
    {Input Query Coin Message : Type}
    [Fintype Input] [Fintype Query] [Fintype Coin] [Fintype Message]
    [DecidableEq Message]
    (coinDistribution : FiniteDistribution Coin)
    (encode : Coin → Input → Message)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) : ℝ :=
  ∑ coin, coinDistribution.mass coin *
    ∑ query, queryDistribution.mass query *
      ∑ message : Message,
        |∑ input, inputDistribution.mass input *
          (if encode coin input = message
            then problem.character query input else 0)|

theorem structuredAdvantage_toFinDistribution
    {Input Query Coin Message : Type}
    [Fintype Input] [Fintype Query] [Fintype Coin] [Fintype Message]
    [DecidableEq Message]
    (coinDistribution : FiniteDistribution Coin)
    (encode : Coin → Input → Message)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    structuredAdvantage
        (toFinDistribution Coin coinDistribution)
        (fun index input ↦ encode (decodeFinSeed Coin index) input)
        problem inputDistribution queryDistribution =
      outcomeStructuredAdvantage coinDistribution encode problem
        inputDistribution queryDistribution := by
  let payoff : Coin → ℝ := fun coin ↦ coinDistribution.mass coin *
    ∑ query, queryDistribution.mass query *
      ∑ message : Message,
        |∑ input, inputDistribution.mass input *
          (if encode coin input = message
            then problem.character query input else 0)|
  change (∑ index, payoff (decodeFinSeed Coin index)) =
    ∑ coin, payoff coin
  simpa only [decodeFinSeed] using
    ((Fintype.equivFin Coin).symm.sum_comp payoff)

theorem exists_protocol_of_outcomeCoin_structured_card_le
    {Input Query Coin Message : Type}
    [Fintype Input] [Fintype Query] [Fintype Coin] [Fintype Message]
    [DecidableEq Message] [Nonempty Message]
    {messageBits : Nat}
    (coinDistribution : FiniteDistribution Coin)
    (encode : Coin → Input → Message)
    (hcard : Fintype.card Message ≤ 2 ^ messageBits)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    ∃ protocol : PublicCoinProtocol Input messageBits (Fintype.card Coin),
      outcomeStructuredAdvantage coinDistribution encode problem
          inputDistribution queryDistribution ≤
        protocol.advantage problem inputDistribution queryDistribution := by
  obtain ⟨protocol, hadvantage⟩ :=
    exists_protocol_of_structured_card_le
      (toFinDistribution Coin coinDistribution)
      (fun index input ↦ encode (decodeFinSeed Coin index) input)
      hcard problem inputDistribution queryDistribution
  refine ⟨protocol, ?_⟩
  rw [← structuredAdvantage_toFinDistribution
    coinDistribution encode problem inputDistribution queryDistribution]
  exact hadvantage

end

end PegSeparation.External.LarsenYuCoinTransport
