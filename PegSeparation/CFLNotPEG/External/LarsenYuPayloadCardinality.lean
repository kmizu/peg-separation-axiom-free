import PegSeparation.CFLNotPEG.External.LarsenYuFiniteMessageEmbedding


namespace PegSeparation.External.LarsenYuPayloadCardinality

noncomputable section

abbrev FixedCellBlock (wordBits blockCells : Nat) :=
  Fin blockCells → (CellProbe.Address wordBits × CellProbe.Word wordBits)

abbrev FixedPayload (wordBits cacheCells blockCells : Nat) :=
  FixedCellBlock wordBits blockCells ×
    FixedCellBlock wordBits blockCells ×
      (Fin cacheCells → CellProbe.Word wordBits) × Bool × Bool

theorem card_bitVec (width : Nat) :
    Fintype.card (BitVec width) = 2 ^ width := by
  calc
    Fintype.card (BitVec width) = Fintype.card (Fin (2 ^ width)) :=
      Fintype.card_congr (BitVec.equivFin :
        BitVec width ≃+* Fin (2 ^ width)).toEquiv
    _ = 2 ^ width := Fintype.card_fin _

theorem card_fixedCellBlock (wordBits blockCells : Nat) :
    Fintype.card (FixedCellBlock wordBits blockCells) =
      2 ^ (2 * blockCells * wordBits) := by
  simp only [FixedCellBlock, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_prod, card_bitVec]
  rw [← pow_add, ← pow_mul]
  congr 1
  ring

theorem card_fixedPayload (wordBits cacheCells blockCells : Nat) :
    Fintype.card (FixedPayload wordBits cacheCells blockCells) =
      2 ^ (4 * blockCells * wordBits + cacheCells * wordBits + 2) := by
  simp only [FixedPayload, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, card_bitVec, Fintype.card_bool]
  have hpair : (2 ^ wordBits : Nat) * 2 ^ wordBits =
      2 ^ (wordBits + wordBits) := (pow_add _ _ _).symm
  simp_rw [hpair]
  simp_rw [← pow_mul (2 : Nat) (wordBits + wordBits) blockCells]
  rw [← pow_mul (2 : Nat) wordBits cacheCells]
  rw [show (2 : Nat) * 2 = 2 ^ 2 by norm_num]
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1
  ring
def payloadEmbedding (wordBits cacheCells blockCells : Nat) :
    FixedPayload wordBits cacheCells blockCells ↪
      BitVec (4 * blockCells * wordBits + cacheCells * wordBits + 2) :=
  LarsenYuFiniteMessageEmbedding.embeddingIntoBitVecOfCardLE
    (FixedPayload wordBits cacheCells blockCells)
    (4 * blockCells * wordBits + cacheCells * wordBits + 2)
    (by rw [card_fixedPayload])

end

end PegSeparation.External.LarsenYuPayloadCardinality
