import PegSeparation.CFLNotPEG.Reduction.SCAPersistentCompiler


namespace PegSeparation.Reduction.GenericPackingBounds

open PegSeparation.CellProbe
open PegSeparation.Reduction.SCAToCellProbe
open PegSeparation.Reduction.ThreeStageModel
open PegSeparation.Reduction.SCAPersistentCompiler

def logWidth (n : ℕ) : ℕ :=
  Nat.clog 2 (n + 1) + 1

def maxNodes (polynomialConstant polynomialExponent n : ℕ) : ℕ :=
  polynomialConstant * (n + 1) ^ polynomialExponent + 1

def wordScale (stateCount workLabelCount degree polynomialConstant
    polynomialExponent : ℕ) : ℕ :=
  stateCount + workLabelCount + degree + polynomialConstant +
    polynomialExponent + 8

def wordBits (stateCount workLabelCount degree polynomialConstant
    polynomialExponent n : ℕ) : ℕ :=
  wordScale stateCount workLabelCount degree polynomialConstant
      polynomialExponent *
    logWidth n

theorem logWidth_pos (n : ℕ) :
    0 < logWidth n := by
  unfold logWidth
  omega

theorem input_le_two_pow_logWidth (n : ℕ) :
    n + 1 ≤ 2 ^ logWidth n := by
  have base :
      n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) :=
    Nat.le_pow_clog Nat.one_lt_two _
  exact base.trans
    (Nat.pow_le_pow_right (by omega)
      (by unfold logWidth; omega))

theorem two_pow_logWidth_le (n : ℕ) :
    2 ^ logWidth n ≤ 4 * (n + 1) := by
  cases n with
  | zero => norm_num [logWidth]
  | succ n =>
      have inputLarge : 1 < n + 1 + 1 := by omega
      have below :=
        Nat.pow_pred_clog_lt_self Nat.one_lt_two inputLarge
      have clogPositive :
          0 < Nat.clog 2 (n + 1 + 1) :=
        Nat.clog_pos Nat.one_lt_two inputLarge
      have exponent :
          Nat.clog 2 (n + 1 + 1) =
            (Nat.clog 2 (n + 1 + 1)).pred + 1 := by
        exact (Nat.succ_pred_eq_of_pos clogPositive).symm
      unfold logWidth
      rw [exponent, pow_succ, pow_succ]
      nlinarith

theorem addressSpace_polynomial_bound
    (stateCount workLabelCount degree polynomialConstant
      polynomialExponent n : ℕ) :
    2 ^ wordBits stateCount workLabelCount degree polynomialConstant
        polynomialExponent n ≤
      4 ^ wordScale stateCount workLabelCount degree polynomialConstant
          polynomialExponent *
        (n + 1) ^
          wordScale stateCount workLabelCount degree polynomialConstant
            polynomialExponent := by
  let scale :=
    wordScale stateCount workLabelCount degree polynomialConstant
      polynomialExponent
  have baseBound := two_pow_logWidth_le n
  have powered :
      (2 ^ logWidth n) ^ scale ≤ (4 * (n + 1)) ^ scale :=
    Nat.pow_le_pow_left baseBound scale
  unfold wordBits
  rw [Nat.pow_mul']
  calc
    (2 ^ logWidth n) ^ scale ≤ (4 * (n + 1)) ^ scale := powered
    _ = 4 ^ scale * (n + 1) ^ scale := by
      rw [Nat.mul_pow]

theorem self_le_two_pow : ∀ value : ℕ, value ≤ 2 ^ value
  | 0 => by simp
  | value + 1 => by
      rw [pow_succ]
      have previous := self_le_two_pow value
      have positive : 1 ≤ 2 ^ value := Nat.one_le_two_pow
      omega

theorem polynomial_le_power
    (polynomialConstant polynomialExponent n : ℕ) :
    polynomialConstant * (n + 1) ^ polynomialExponent ≤
      2 ^ (polynomialConstant +
        logWidth n * polynomialExponent) := by
  have constantBound :
      polynomialConstant ≤ 2 ^ polynomialConstant :=
    self_le_two_pow polynomialConstant
  have inputBound := input_le_two_pow_logWidth n
  have powered :
      (n + 1) ^ polynomialExponent ≤
        (2 ^ logWidth n) ^ polynomialExponent :=
    Nat.pow_le_pow_left inputBound polynomialExponent
  calc
    polynomialConstant * (n + 1) ^ polynomialExponent ≤
        2 ^ polynomialConstant *
          (2 ^ logWidth n) ^ polynomialExponent :=
      Nat.mul_le_mul constantBound powered
    _ = 2 ^ (polynomialConstant +
        logWidth n * polynomialExponent) := by
      rw [← Nat.pow_mul, ← pow_add]

theorem maxNodes_power_bound
    (polynomialConstant polynomialExponent n : ℕ) :
    maxNodes polynomialConstant polynomialExponent n ≤
      2 ^ (polynomialConstant +
        logWidth n * polynomialExponent + 1) := by
  have polynomialBound :=
    polynomial_le_power polynomialConstant polynomialExponent n
  have powerPositive :
      1 ≤ 2 ^ (polynomialConstant +
        logWidth n * polynomialExponent) :=
    Nat.one_le_two_pow
  unfold maxNodes
  rw [pow_succ]
  omega

theorem maxNodes_pos
    (polynomialConstant polynomialExponent n : ℕ) :
    0 < maxNodes polynomialConstant polynomialExponent n := by
  unfold maxNodes
  omega

theorem encodedWord_nodes_fit
    {Terminal : Type} {problem : Problem}
    (encoding : Encoding Terminal problem)
    (n : ℕ) (data : problem.Data n)
    (updates : Fin (problem.updateCount n) → problem.Update n)
    (finalQuery : problem.Query n) :
    (encoding.word n data updates finalQuery).length + 1 ≤
      maxNodes encoding.polynomialConstant encoding.polynomialExponent n := by
  unfold maxNodes
  exact Nat.add_le_add_right
    (encoding.total_length n data updates finalQuery) 1

theorem wordBits_exponent_bound
    (stateCount workLabelCount degree polynomialConstant
      polynomialExponent n : ℕ) :
    polynomialConstant + degree + 4 +
        logWidth n * polynomialExponent ≤
      wordBits stateCount workLabelCount degree polynomialConstant
        polynomialExponent n := by
  have widthOne : 1 ≤ logWidth n := logWidth_pos n
  have fixedBound :
      polynomialConstant + degree + 4 ≤
        (polynomialConstant + degree + 4) * logWidth n := by
    simpa using
      Nat.mul_le_mul_left (polynomialConstant + degree + 4) widthOne
  unfold wordBits wordScale
  calc
    polynomialConstant + degree + 4 +
          logWidth n * polynomialExponent ≤
        (polynomialConstant + degree + 4) * logWidth n +
          logWidth n * polynomialExponent := by omega
    _ = (polynomialConstant + degree + 4 +
          polynomialExponent) * logWidth n := by ring
    _ ≤ (stateCount + workLabelCount + degree +
          polynomialConstant + polynomialExponent + 8) *
          logWidth n := by
      exact Nat.mul_le_mul_right _ (by omega)

theorem state_exponent_bound
    (stateCount workLabelCount degree polynomialConstant
      polynomialExponent n : ℕ) :
    stateCount ≤
      wordBits stateCount workLabelCount degree polynomialConstant
        polynomialExponent n := by
  have widthOne : 1 ≤ logWidth n := logWidth_pos n
  unfold wordBits wordScale
  calc
    stateCount ≤ stateCount * logWidth n := by
      simpa using Nat.mul_le_mul_left stateCount widthOne
    _ ≤ (stateCount + workLabelCount + degree +
          polynomialConstant + polynomialExponent + 8) *
          logWidth n := by
      exact Nat.mul_le_mul_right _ (by omega)

theorem label_exponent_bound
    (stateCount workLabelCount degree polynomialConstant
      polynomialExponent n : ℕ) :
    workLabelCount + 1 ≤
      wordBits stateCount workLabelCount degree polynomialConstant
        polynomialExponent n := by
  have widthOne : 1 ≤ logWidth n := logWidth_pos n
  unfold wordBits wordScale
  calc
    workLabelCount + 1 ≤ (workLabelCount + 1) * logWidth n := by
      simpa using Nat.mul_le_mul_left (workLabelCount + 1) widthOne
    _ ≤ (stateCount + workLabelCount + degree +
          polynomialConstant + polynomialExponent + 8) *
          logWidth n := by
      exact Nat.mul_le_mul_right _ (by omega)

theorem logicalAddress_card
    (nodes degree : ℕ) :
    Fintype.card (LogicalAddress nodes degree) =
      1 + nodes + nodes * degree := by
  let equivalence :
      LogicalAddress nodes degree ≃
        Unit ⊕ (Fin nodes ⊕ (Fin nodes × Fin degree)) :=
    { toFun := fun
        | .state => .inl ()
        | .nodeLabel node => .inr (.inl node)
        | .nodeEdge node port => .inr (.inr (node, port))
      invFun := fun
        | .inl _ => .state
        | .inr (.inl node) => .nodeLabel node
        | .inr (.inr pair) => .nodeEdge pair.1 pair.2
      left_inv := by
        intro value
        cases value <;> rfl
      right_inv := by
        intro value
        rcases value with (_ | value)
        · rfl
        · rcases value with (_ | value) <;> rfl }
  rw [Fintype.card_congr equivalence]
  simp
  omega

theorem core_address_capacity_strict
    (stateCount workLabelCount degree polynomialConstant
      polynomialExponent n : ℕ) :
    Fintype.card
        (LogicalAddress
          (maxNodes polynomialConstant polynomialExponent n) degree) <
      2 ^ wordBits stateCount workLabelCount degree polynomialConstant
        polynomialExponent n := by
  let nodes := maxNodes polynomialConstant polynomialExponent n
  let width := logWidth n
  have nodesPositive : 0 < nodes :=
    maxNodes_pos polynomialConstant polynomialExponent n
  have cardBound :
      1 + nodes + nodes * degree ≤ (degree + 2) * nodes := by
    nlinarith
  have degreeBound : degree + 2 ≤ 2 ^ (degree + 2) :=
    self_le_two_pow (degree + 2)
  have nodesBound :
      nodes ≤
        2 ^ (polynomialConstant + width * polynomialExponent + 1) := by
    exact maxNodes_power_bound polynomialConstant polynomialExponent n
  have productBound :
      (degree + 2) * nodes ≤
        2 ^ (degree + 2) *
          2 ^ (polynomialConstant + width * polynomialExponent + 1) :=
    Nat.mul_le_mul degreeBound nodesBound
  have exponentBound :
      degree + 2 +
          (polynomialConstant + width * polynomialExponent + 1) + 1 ≤
        wordBits stateCount workLabelCount degree polynomialConstant
          polynomialExponent n := by
    dsimp [width]
    have := wordBits_exponent_bound stateCount workLabelCount degree
      polynomialConstant polynomialExponent n
    omega
  rw [logicalAddress_card]
  calc
    1 + nodes + nodes * degree ≤ (degree + 2) * nodes := cardBound
    _ ≤ 2 ^ (degree + 2) *
          2 ^ (polynomialConstant + width * polynomialExponent + 1) :=
      productBound
    _ = 2 ^ (degree + 2 +
          (polynomialConstant + width * polynomialExponent + 1)) := by
      rw [← pow_add]
    _ < 2 ^ wordBits stateCount workLabelCount degree polynomialConstant
          polynomialExponent n := by
      exact Nat.pow_lt_pow_right (by omega) (by omega)

theorem count_capacity
    (stateCount workLabelCount degree polynomialConstant
      polynomialExponent n : ℕ) :
    maxNodes polynomialConstant polynomialExponent n + 1 ≤
      2 ^ wordBits stateCount workLabelCount degree polynomialConstant
        polynomialExponent n := by
  let nodes := maxNodes polynomialConstant polynomialExponent n
  let width := logWidth n
  have nodesPositive : 0 < nodes :=
    maxNodes_pos polynomialConstant polynomialExponent n
  have nodesBound :
      nodes ≤
        2 ^ (polynomialConstant + width * polynomialExponent + 1) := by
    exact maxNodes_power_bound polynomialConstant polynomialExponent n
  have sumBound : nodes + 1 ≤ 2 * nodes := by omega
  have exponentBound :
      polynomialConstant + width * polynomialExponent + 2 ≤
        wordBits stateCount workLabelCount degree polynomialConstant
          polynomialExponent n := by
    have wide := wordBits_exponent_bound stateCount workLabelCount degree
      polynomialConstant polynomialExponent n
    dsimp [width]
    omega
  calc
    nodes + 1 ≤ 2 * nodes := sumBound
    _ ≤ 2 * 2 ^
          (polynomialConstant + width * polynomialExponent + 1) :=
      Nat.mul_le_mul_left 2 nodesBound
    _ = 2 ^ (polynomialConstant + width * polynomialExponent + 2) := by
      rw [show polynomialConstant + width * polynomialExponent + 2 =
        (polynomialConstant + width * polynomialExponent + 1) + 1 by omega]
      rw [pow_succ]
      ring
    _ ≤ 2 ^ wordBits stateCount workLabelCount degree polynomialConstant
          polynomialExponent n :=
      Nat.pow_le_pow_right (by omega) exponentBound

noncomputable def corePacking
    (stateCount workLabelCount degree polynomialConstant
      polynomialExponent n : ℕ) :
    Packing
      (wordBits stateCount workLabelCount degree polynomialConstant
        polynomialExponent n)
      (maxNodes polynomialConstant polynomialExponent n)
      stateCount workLabelCount degree where
  addressCapacity :=
    Nat.le_of_lt
      (core_address_capacity_strict stateCount workLabelCount degree
        polynomialConstant polynomialExponent n)
  stateCapacity :=
    (self_le_two_pow stateCount).trans
      (Nat.pow_le_pow_right (by omega)
        (state_exponent_bound stateCount workLabelCount degree
          polynomialConstant polynomialExponent n))
  labelCapacity := by
    simp only [Fintype.card_option, Fintype.card_fin]
    exact
      (self_le_two_pow (workLabelCount + 1)).trans
        (Nat.pow_le_pow_right (by omega)
          (label_exponent_bound stateCount workLabelCount degree
            polynomialConstant polynomialExponent n))
  offsetCapacity := by
    simp only [Fintype.card_option, Fintype.card_fin]
    exact count_capacity stateCount workLabelCount degree
      polynomialConstant polynomialExponent n

theorem exists_fresh_address
    (stateCount workLabelCount degree polynomialConstant
      polynomialExponent n : ℕ) :
    ∃ address :
        CellProbe.Address
          (wordBits stateCount workLabelCount degree polynomialConstant
            polynomialExponent n),
      ∀ logical :
          LogicalAddress
            (maxNodes polynomialConstant polynomialExponent n) degree,
        (corePacking stateCount workLabelCount degree polynomialConstant
          polynomialExponent n).address logical ≠ address := by
  classical
  let packing :=
    corePacking stateCount workLabelCount degree polynomialConstant
      polynomialExponent n
  by_contra noFresh
  push Not at noFresh
  have surjective : Function.Surjective packing.address := by
    intro address
    rcases noFresh address with ⟨logical, equality⟩
    exact ⟨logical, equality⟩
  have cardinality :=
    Fintype.card_le_of_surjective packing.address surjective
  have strict := core_address_capacity_strict stateCount workLabelCount degree
    polynomialConstant polynomialExponent n
  have reverse :
      2 ^ wordBits stateCount workLabelCount degree polynomialConstant
          polynomialExponent n ≤
        Fintype.card
          (LogicalAddress
            (maxNodes polynomialConstant polynomialExponent n) degree) := by
    have bitVecCard :
        Fintype.card
            (CellProbe.Address
              (wordBits stateCount workLabelCount degree polynomialConstant
                polynomialExponent n)) =
          2 ^ wordBits stateCount workLabelCount degree polynomialConstant
            polynomialExponent n := by
      calc
        Fintype.card
              (CellProbe.Address
                (wordBits stateCount workLabelCount degree
                  polynomialConstant polynomialExponent n)) =
            Fintype.card
              (Fin
                (2 ^ wordBits stateCount workLabelCount degree
                  polynomialConstant polynomialExponent n)) :=
          Fintype.card_congr
            (BitVec.equivFin :
              BitVec
                  (wordBits stateCount workLabelCount degree
                    polynomialConstant polynomialExponent n) ≃+*
                Fin
                  (2 ^ wordBits stateCount workLabelCount degree
                    polynomialConstant polynomialExponent n)).toEquiv
        _ = 2 ^ wordBits stateCount workLabelCount degree
              polynomialConstant polynomialExponent n :=
          Fintype.card_fin _
    rw [bitVecCard] at cardinality
    exact cardinality
  omega

noncomputable def countedPacking
    (stateCount workLabelCount degree polynomialConstant
      polynomialExponent n : ℕ) :
    CountedPacking
      (wordBits stateCount workLabelCount degree polynomialConstant
        polynomialExponent n)
      (maxNodes polynomialConstant polynomialExponent n)
      stateCount workLabelCount degree := by
  let witness :=
    exists_fresh_address stateCount workLabelCount degree
      polynomialConstant polynomialExponent n
  exact
    { core :=
        corePacking stateCount workLabelCount degree polynomialConstant
          polynomialExponent n
      countAddress := Classical.choose witness
      countFresh := Classical.choose_spec witness
      countCapacity :=
        count_capacity stateCount workLabelCount degree polynomialConstant
          polynomialExponent n }

end PegSeparation.Reduction.GenericPackingBounds
