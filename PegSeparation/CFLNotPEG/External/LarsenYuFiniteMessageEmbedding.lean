import PegSeparation.CFLNotPEG.External.LarsenYuConditionalJensen


open scoped BigOperators

namespace PegSeparation.External.LarsenYuFiniteMessageEmbedding

noncomputable section

open LarsenYuConditionalJensen

def structuredAdvantage
    {Input Query Message : Type}
    [Fintype Input] [Fintype Query] [Fintype Message] [DecidableEq Message]
    {coinCount : Nat}
    (coinDistribution : FiniteDistribution (Fin coinCount))
    (encode : Fin coinCount → Input → Message)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) : ℝ :=
  ∑ coin, coinDistribution.mass coin *
    ∑ query, queryDistribution.mass query *
      ∑ message : Message,
        |∑ input, inputDistribution.mass input *
          (if encode coin input = message then problem.character query input else 0)|

def protocolOfEmbedding
    {Input Message : Type} {messageBits coinCount : Nat}
    (coinDistribution : FiniteDistribution (Fin coinCount))
    (encode : Fin coinCount → Input → Message)
    (embedding : Message ↪ BitVec messageBits) :
    PublicCoinProtocol Input messageBits coinCount where
  coinDistribution := coinDistribution
  encode := fun coin input ↦ embedding (encode coin input)

theorem exists_embeddingDecoder
    {Message : Type} [Nonempty Message] {messageBits : Nat}
    (embedding : Message ↪ BitVec messageBits) :
    ∃ decode : BitVec messageBits → Message,
      ∀ message, decode (embedding message) = message := by
  classical
  exact ⟨Function.invFun embedding,
    Function.leftInverse_invFun embedding.injective⟩

theorem structuredAdvantage_le_protocolOfEmbedding_advantage
    {Input Query Message : Type}
    [Fintype Input] [Fintype Query] [Fintype Message]
    [DecidableEq Message] [Nonempty Message]
    {messageBits coinCount : Nat}
    (coinDistribution : FiniteDistribution (Fin coinCount))
    (encode : Fin coinCount → Input → Message)
    (embedding : Message ↪ BitVec messageBits)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    structuredAdvantage coinDistribution encode problem inputDistribution
        queryDistribution ≤
      (protocolOfEmbedding coinDistribution encode embedding).advantage
        problem inputDistribution queryDistribution := by
  classical
  obtain ⟨decode, hdecode⟩ := exists_embeddingDecoder embedding
  unfold structuredAdvantage PublicCoinProtocol.advantage
    protocolOfEmbedding
  apply Finset.sum_le_sum
  intro coin _hcoin
  apply mul_le_mul_of_nonneg_left _
    (coinDistribution.mass_nonnegative coin)
  apply Finset.sum_le_sum
  intro query _hquery
  apply mul_le_mul_of_nonneg_left _
    (queryDistribution.mass_nonnegative query)
  exact partitionL1_mono_of_factor
    inputDistribution.mass (problem.character query)
    (encode coin) (fun input ↦ embedding (encode coin input))
    decode (fun input ↦ hdecode (encode coin input))

def embeddingIntoBitVecOfCardLE
    (Message : Type) [Fintype Message] (messageBits : Nat)
    (hcard : Fintype.card Message ≤ 2 ^ messageBits) :
    Message ↪ BitVec messageBits := by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  have hbitvec : Fintype.card (BitVec messageBits) = 2 ^ messageBits := by
    calc
      Fintype.card (BitVec messageBits) =
          Fintype.card (Fin (2 ^ messageBits)) :=
        Fintype.card_congr (BitVec.equivFin :
          BitVec messageBits ≃+* Fin (2 ^ messageBits)).toEquiv
      _ = 2 ^ messageBits := Fintype.card_fin _
  rw [hbitvec]
  exact hcard

theorem exists_protocol_of_structured_card_le
    {Input Query Message : Type}
    [Fintype Input] [Fintype Query] [Fintype Message]
    [DecidableEq Message] [Nonempty Message]
    {messageBits coinCount : Nat}
    (coinDistribution : FiniteDistribution (Fin coinCount))
    (encode : Fin coinCount → Input → Message)
    (hcard : Fintype.card Message ≤ 2 ^ messageBits)
    (problem : BinaryProblem Input Query)
    (inputDistribution : FiniteDistribution Input)
    (queryDistribution : FiniteDistribution Query) :
    ∃ protocol : PublicCoinProtocol Input messageBits coinCount,
      structuredAdvantage coinDistribution encode problem inputDistribution
          queryDistribution ≤
        protocol.advantage problem inputDistribution queryDistribution := by
  let embedding := embeddingIntoBitVecOfCardLE Message messageBits hcard
  refine ⟨protocolOfEmbedding coinDistribution encode embedding, ?_⟩
  exact structuredAdvantage_le_protocolOfEmbedding_advantage
    coinDistribution encode embedding problem inputDistribution queryDistribution

end

end PegSeparation.External.LarsenYuFiniteMessageEmbedding
