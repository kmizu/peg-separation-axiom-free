import PegSeparation.CFLNotPEG.Reduction.HardMultiphase
import PegSeparation.CFLNotPEG.Reduction.MultiphaseModel


namespace PegSeparation.Reduction.SCAPackingBounds

open PegSeparation.Reduction.SCAToCellProbe
open PegSeparation.Reduction.HardMultiphase
open PegSeparation.Reduction.MultiphaseModel
open PegSeparation.Witness.HardSlice

def base (n : ℕ) : ℕ := 2 ^ logScale n

def maxNodes (n : ℕ) : ℕ := 2 ^ (8 * logScale n)

def wordScale (stateCount workLabelCount degree : ℕ) : ℕ :=
  12 + stateCount + workLabelCount + degree

def wordBits (stateCount workLabelCount degree n : ℕ) : ℕ :=
  scaledLogBudget (wordScale stateCount workLabelCount degree) n

theorem logScale_pos (n : ℕ) : 0 < logScale n := by
  unfold logScale
  omega

theorem base_ge_two (n : ℕ) : 2 ≤ base n := by
  unfold base
  have exponent : 1 ≤ logScale n := logScale_pos n
  have := Nat.pow_le_pow_right (show 0 < 2 by omega) exponent
  simpa using this

theorem n_le_base (n : ℕ) : n ≤ base n := by
  have logarithmic : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) :=
    Nat.le_pow_clog Nat.one_lt_two _
  have exponent : Nat.clog 2 (n + 1) ≤ logScale n := by
    unfold logScale
    omega
  have powers := Nat.pow_le_pow_right (show 0 < 2 by omega) exponent
  unfold base
  omega

theorem self_le_two_pow : ∀ value : ℕ, value ≤ 2 ^ value
  | 0 => by simp
  | value + 1 => by
      rw [pow_succ]
      have previous := self_le_two_pow value
      have positive : 1 ≤ 2 ^ value := Nat.one_le_two_pow
      omega

theorem maxNodes_eq_base_pow (n : ℕ) :
    maxNodes n = (base n) ^ 8 := by
  unfold maxNodes base
  rw [← Nat.pow_mul]
  congr 1
  omega

theorem hard_nodes_fit (n : ℕ) :
    rowCount n * (keyWidth n + n + 3) + 2 + n + (keyWidth n + 1) ≤
      maxNodes n := by
  let scale := logScale n
  let bound := base n
  have scalePos : 0 < scale := logScale_pos n
  have boundTwo : 2 ≤ bound := base_ge_two n
  have nBound : n ≤ bound := n_le_base n
  have rowBound : rowCount n ≤ bound ^ 2 := by
    simp only [rowCount]
    exact Nat.pow_le_pow_left nBound 2
  have keyLinear : keyWidth n ≤ 2 * scale := by
    rw [keyWidth_eq_indexWidth]
    have := indexWidth_le_two_clog n
    dsimp [scale, logScale]
    omega
  have linearPower : 2 * scale ≤ 2 ^ (2 * scale) :=
    self_le_two_pow (2 * scale)
  have squareIdentity : 2 ^ (2 * scale) = bound ^ 2 := by
    dsimp [bound, base]
    rw [← Nat.pow_mul]
    congr 1
    omega
  have keyBound : keyWidth n ≤ bound ^ 2 := by
    rw [squareIdentity] at linearPower
    exact keyLinear.trans linearPower
  have factorBound : keyWidth n + n + 3 ≤ bound ^ 2 + bound + 3 := by
    omega
  have productBound :
      rowCount n * (keyWidth n + n + 3) ≤
        bound ^ 2 * (bound ^ 2 + bound + 3) :=
    Nat.mul_le_mul rowBound factorBound
  have totalBound :
      rowCount n * (keyWidth n + n + 3) + 2 + n +
          (keyWidth n + 1) ≤
        bound ^ 4 + bound ^ 3 + 4 * bound ^ 2 + bound + 3 := by
    nlinarith
  have boundPos : 0 < bound := by omega
  have pow1 : bound ≤ bound ^ 4 := by
    simpa using Nat.pow_le_pow_right boundPos (show 1 ≤ 4 by omega)
  have pow2 : bound ^ 2 ≤ bound ^ 4 :=
    Nat.pow_le_pow_right boundPos (show 2 ≤ 4 by omega)
  have pow3 : bound ^ 3 ≤ bound ^ 4 :=
    Nat.pow_le_pow_right boundPos (show 3 ≤ 4 by omega)
  have three : 3 ≤ 3 * bound ^ 4 := by
    have positive : 0 < bound ^ 4 := pow_pos boundPos _
    omega
  have tenFourth :
      bound ^ 4 + bound ^ 3 + 4 * bound ^ 2 + bound + 3 ≤
        10 * bound ^ 4 := by
    omega
  have sixteen : 16 ≤ bound ^ 4 := by
    have := Nat.pow_le_pow_left boundTwo 4
    norm_num at this
    exact this
  have ten : 10 ≤ bound ^ 4 := by omega
  have fourthToEighth : 10 * bound ^ 4 ≤ bound ^ 8 := by
    calc
      10 * bound ^ 4 ≤ bound ^ 4 * bound ^ 4 :=
        Nat.mul_le_mul_right (bound ^ 4) ten
      _ = bound ^ 8 := by ring
  rw [maxNodes_eq_base_pow]
  exact totalBound.trans (tenFourth.trans fourthToEighth)

def logicalAddressEquiv (nodes degree : ℕ) :
    LogicalAddress nodes degree ≃
      Unit ⊕ (Fin nodes ⊕ (Fin nodes × Fin degree)) where
  toFun
    | .state => .inl ()
    | .nodeLabel node => .inr (.inl node)
    | .nodeEdge node port => .inr (.inr (node, port))
  invFun
    | .inl _ => .state
    | .inr (.inl node) => .nodeLabel node
    | .inr (.inr (node, port)) => .nodeEdge node port
  left_inv value := by cases value <;> rfl
  right_inv value := by
    rcases value with (_ | value)
    · rfl
    · rcases value with (_ | value) <;> rfl

theorem logicalAddress_card (nodes degree : ℕ) :
    Fintype.card (LogicalAddress nodes degree) =
      1 + nodes + nodes * degree := by
  rw [Fintype.card_congr (logicalAddressEquiv nodes degree)]
  simp
  omega

theorem word_exponent_ge_nodes
    (stateCount workLabelCount degree n : ℕ) :
    8 * logScale n + degree + 2 ≤
      wordBits stateCount workLabelCount degree n := by
  unfold wordBits scaledLogBudget wordScale
  have scaleOne : 1 ≤ logScale n := logScale_pos n
  have constant : degree + 2 ≤ (degree + 2) * logScale n := by
    simpa using Nat.mul_le_mul_left (degree + 2) scaleOne
  have coefficient : degree + 10 ≤
      12 + stateCount + workLabelCount + degree := by omega
  calc
    8 * logScale n + degree + 2 ≤
        8 * logScale n + (degree + 2) * logScale n := by omega
    _ = (degree + 10) * logScale n := by ring
    _ ≤ (12 + stateCount + workLabelCount + degree) * logScale n :=
      Nat.mul_le_mul_right _ coefficient

theorem word_exponent_ge_state
    (stateCount workLabelCount degree n : ℕ) :
    stateCount ≤ wordBits stateCount workLabelCount degree n := by
  unfold wordBits scaledLogBudget wordScale
  have scaleOne : 1 ≤ logScale n := logScale_pos n
  have scaled : stateCount ≤ stateCount * logScale n := by
    simpa using Nat.mul_le_mul_left stateCount scaleOne
  exact scaled.trans (Nat.mul_le_mul_right _ (by omega))

theorem word_exponent_ge_label
    (stateCount workLabelCount degree n : ℕ) :
    workLabelCount + 1 ≤ wordBits stateCount workLabelCount degree n := by
  unfold wordBits scaledLogBudget wordScale
  have scaleOne : 1 ≤ logScale n := logScale_pos n
  have scaled : workLabelCount + 1 ≤
      (workLabelCount + 1) * logScale n := by
    simpa using Nat.mul_le_mul_left (workLabelCount + 1) scaleOne
  exact scaled.trans (Nat.mul_le_mul_right _ (by omega))

noncomputable def packing
    (stateCount workLabelCount degree n : ℕ) :
    Packing (wordBits stateCount workLabelCount degree n) (maxNodes n)
      stateCount workLabelCount degree :=
  { addressCapacity := by
      rw [logicalAddress_card]
      have nodesPositive : 0 < maxNodes n := by
        unfold maxNodes
        positivity
      have cardBound :
          1 + maxNodes n + maxNodes n * degree ≤
            (degree + 2) * maxNodes n := by
        nlinarith
      have degreeBound : degree + 2 ≤ 2 ^ (degree + 2) :=
        self_le_two_pow (degree + 2)
      have productBound :
          (degree + 2) * maxNodes n ≤
            2 ^ (degree + 2) * 2 ^ (8 * logScale n) := by
        unfold maxNodes
        exact Nat.mul_le_mul degreeBound le_rfl
      have exponentBound := word_exponent_ge_nodes
        stateCount workLabelCount degree n
      calc
        1 + maxNodes n + maxNodes n * degree ≤
            (degree + 2) * maxNodes n := cardBound
        _ ≤ 2 ^ (degree + 2) * 2 ^ (8 * logScale n) := productBound
        _ = 2 ^ (8 * logScale n + degree + 2) := by
          rw [← pow_add]
          congr 1
          omega
        _ ≤ 2 ^ wordBits stateCount workLabelCount degree n :=
          Nat.pow_le_pow_right (show 0 < 2 by omega) exponentBound
    stateCapacity := by
      exact (self_le_two_pow stateCount).trans
        (Nat.pow_le_pow_right (show 0 < 2 by omega)
          (word_exponent_ge_state stateCount workLabelCount degree n))
    labelCapacity := by
      simp only [Fintype.card_option, Fintype.card_fin]
      exact (self_le_two_pow (workLabelCount + 1)).trans
        (Nat.pow_le_pow_right (show 0 < 2 by omega)
          (word_exponent_ge_label stateCount workLabelCount degree n))
    offsetCapacity := by
      simp only [Fintype.card_option, Fintype.card_fin]
      have positive : 1 ≤ maxNodes n := by
        unfold maxNodes
        exact Nat.one_le_two_pow
      have sumBound : maxNodes n + 1 ≤ 2 * maxNodes n := by omega
      have exponentBound :
          8 * logScale n + 1 ≤
            wordBits stateCount workLabelCount degree n := by
        exact (by omega : 8 * logScale n + 1 ≤
          8 * logScale n + degree + 2).trans
            (word_exponent_ge_nodes stateCount workLabelCount degree n)
      calc
        maxNodes n + 1 ≤ 2 * maxNodes n := sumBound
        _ = 2 ^ (8 * logScale n + 1) := by
          unfold maxNodes
          rw [pow_succ]
          ring
        _ ≤ 2 ^ wordBits stateCount workLabelCount degree n :=
          Nat.pow_le_pow_right (show 0 < 2 by omega) exponentBound }

end PegSeparation.Reduction.SCAPackingBounds
