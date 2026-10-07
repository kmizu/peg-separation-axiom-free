import Mathlib


namespace PegSeparation.LowerBound.Chronogram

open scoped BigOperators


def middleEpochs (ell : ℕ) : Finset ℕ :=
  Finset.Icc ((ell + 2) / 3) ((5 * ell) / 6)

@[simp] theorem mem_middleEpochs {ell i : ℕ} :
    i ∈ middleEpochs ell ↔ (ell + 2) / 3 ≤ i ∧ i ≤ (5 * ell) / 6 := by
  simp [middleEpochs]

@[simp] theorem card_middleEpochs (ell : ℕ) :
    (middleEpochs ell).card = (5 * ell) / 6 + 1 - (ell + 2) / 3 := by
  simp [middleEpochs]

theorem middleEpochs_nonempty {ell : ℕ} (hell : 2 ≤ ell) :
    (middleEpochs ell).Nonempty := by
  rw [middleEpochs, Finset.nonempty_Icc]
  omega

def peeledMass (gamma ell : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ico 1 ell, gamma ^ j

theorem peeledMass_succ {gamma j : ℕ} (hj : 1 ≤ j) :
    peeledMass gamma (j + 1) = peeledMass gamma j + gamma ^ j := by
  exact Finset.sum_Ico_succ_top hj (fun k => gamma ^ k)

theorem peeledMass_mono (gamma : ℕ) {a b : ℕ} (hab : a ≤ b) :
    peeledMass gamma a ≤ peeledMass gamma b := by
  apply Finset.sum_le_sum_of_subset
  intro j hj
  simp only [Finset.mem_Ico] at hj ⊢
  exact ⟨hj.1, hj.2.trans_le hab⟩

def epochOffsets (gamma j : ℕ) : Finset ℕ :=
  Finset.Ico (peeledMass gamma j) (peeledMass gamma (j + 1))

@[simp] theorem card_epochOffsets {gamma j : ℕ} (hj : 1 ≤ j) :
    (epochOffsets gamma j).card = gamma ^ j := by
  simp [epochOffsets, peeledMass_succ hj]

theorem epochOffsets_disjoint {gamma i j : ℕ} (hij : i ≠ j) :
    Disjoint (epochOffsets gamma i) (epochOffsets gamma j) := by
  wlog hijlt : i < j generalizing i j
  · have hji : j < i := by omega
    exact (this hij.symm hji).symm
  rw [Finset.disjoint_left]
  intro x hxi hxj
  simp only [epochOffsets, Finset.mem_Ico] at hxi hxj
  have hm : peeledMass gamma (i + 1) ≤ peeledMass gamma j :=
    peeledMass_mono gamma (by omega)
  omega

def geometricCover (gamma ell : ℕ) : Finset ℕ :=
  (Finset.Ico 1 ell).biUnion (epochOffsets gamma)

theorem card_geometricCover (gamma ell : ℕ) :
    (geometricCover gamma ell).card = peeledMass gamma ell := by
  rw [geometricCover, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro j hj
    exact card_epochOffsets (Finset.mem_Ico.mp hj).1
  · intro i hi j hj hij
    exact epochOffsets_disjoint hij

theorem geometricCover_subset_range (gamma ell : ℕ) :
    geometricCover gamma ell ⊆ Finset.range (peeledMass gamma ell) := by
  intro x hx
  simp only [geometricCover, Finset.mem_biUnion] at hx
  obtain ⟨j, hj, hxj⟩ := hx
  rw [epochOffsets] at hxj
  simp only [Finset.mem_Ico] at hj hxj
  simp only [Finset.mem_range]
  exact hxj.2.trans_le (peeledMass_mono gamma (by omega))

theorem geometricCover_eq_range (gamma ell : ℕ) :
    geometricCover gamma ell = Finset.range (peeledMass gamma ell) := by
  apply Finset.eq_of_subset_of_card_le (geometricCover_subset_range gamma ell)
  simp [card_geometricCover]

def residualOffsets (n gamma ell : ℕ) : Finset ℕ :=
  Finset.Ico (peeledMass gamma ell) n

theorem geometricCover_union_residual {n gamma ell : ℕ}
    (hfit : peeledMass gamma ell ≤ n) :
    geometricCover gamma ell ∪ residualOffsets n gamma ell = Finset.range n := by
  rw [geometricCover_eq_range]
  ext x
  simp only [Finset.mem_union, Finset.mem_range, residualOffsets, Finset.mem_Ico]
  omega

theorem geometricCover_disjoint_residual {n gamma ell : ℕ} :
    Disjoint (geometricCover gamma ell) (residualOffsets n gamma ell) := by
  rw [Finset.disjoint_left]
  intro x hcover hresidual
  rw [geometricCover_eq_range] at hcover
  simp only [Finset.mem_range] at hcover
  simp only [residualOffsets, Finset.mem_Ico] at hresidual
  omega

private theorem sum_powers_lt_power {gamma : ℕ} (hgamma : 2 ≤ gamma) :
    ∀ ell : ℕ, (∑ j ∈ Finset.range ell, gamma ^ j) < gamma ^ ell := by
  intro ell
  induction ell with
  | zero => simp
  | succ ell ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hpos : 0 < gamma ^ ell := pow_pos (by omega) _
      have htwo : 2 * gamma ^ ell ≤ gamma * gamma ^ ell := by
        exact Nat.mul_le_mul_right (gamma ^ ell) hgamma
      calc
        (∑ j ∈ Finset.range ell, gamma ^ j) + gamma ^ ell <
            gamma ^ ell + gamma ^ ell := Nat.add_lt_add_right ih _
        _ = 2 * gamma ^ ell := by omega
        _ ≤ gamma * gamma ^ ell := htwo
        _ = gamma ^ ell * gamma := Nat.mul_comm _ _

theorem peeledMass_lt_power {gamma ell : ℕ} (hgamma : 2 ≤ gamma) :
    peeledMass gamma ell < gamma ^ ell := by
  have hsubset : Finset.Ico 1 ell ⊆ Finset.range ell := by
    intro j hj
    simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢
    exact hj.2
  exact (Finset.sum_le_sum_of_subset hsubset).trans_lt
    (sum_powers_lt_power hgamma ell)

theorem peeledMass_lt_updates {gamma ell n : ℕ} (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n) : peeledMass gamma ell < n :=
  (peeledMass_lt_power hgamma).trans_le hpower

theorem peeledMass_succ_le_two_mul_prev {gamma : ℕ} (hgamma : 2 ≤ gamma) :
    ∀ k : ℕ, peeledMass gamma (k + 1) ≤ 2 * gamma ^ k := by
  intro k
  induction k with
  | zero => simp [peeledMass]
  | succ k ih =>
      rw [peeledMass_succ (by omega)]
      have hstep : 2 * gamma ^ k ≤ gamma ^ (k + 1) := by
        rw [pow_succ]
        simpa [Nat.mul_comm] using Nat.mul_le_mul_right (gamma ^ k) hgamma
      calc
        peeledMass gamma (k + 1) + gamma ^ (k + 1) ≤
            2 * gamma ^ k + gamma ^ (k + 1) := Nat.add_le_add_right ih _
        _ ≤ gamma ^ (k + 1) + gamma ^ (k + 1) := Nat.add_le_add_right hstep _
        _ = 2 * gamma ^ (k + 1) := by omega

theorem recent_write_occurrences_bound {gamma : ℕ} (hgamma : 2 ≤ gamma)
    (tu k : ℕ) :
    (∑ j ∈ Finset.Ico 1 (k + 1), tu * gamma ^ j) ≤
      2 * tu * gamma ^ k := by
  calc
    (∑ j ∈ Finset.Ico 1 (k + 1), tu * gamma ^ j) =
        tu * peeledMass gamma (k + 1) := by
      rw [peeledMass, Finset.mul_sum]
    _ ≤ tu * (2 * gamma ^ k) :=
      Nat.mul_le_mul_left tu (peeledMass_succ_le_two_mul_prev hgamma k)
    _ = 2 * tu * gamma ^ k := by
      simp [Nat.mul_comm, Nat.mul_left_comm]

theorem recent_write_occurrences_div_bound {gamma : ℕ} (hgamma : 2 ≤ gamma)
    (tu i : ℕ) (hi : 1 ≤ i) :
    (∑ j ∈ Finset.Ico 1 i, tu * gamma ^ j) ≤
      2 * tu * (gamma ^ i / gamma) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [Nat.add_comm 1 k, pow_succ,
    Nat.mul_div_cancel (gamma ^ k) (by omega : 0 < gamma)]
  exact recent_write_occurrences_bound hgamma tu k

theorem middle_epoch_power_bounds {gamma ell i : ℕ} (hgamma : 1 ≤ gamma)
    (hi : i ∈ middleEpochs ell) :
    gamma ^ ((ell + 2) / 3) ≤ gamma ^ i ∧
      gamma ^ i ≤ gamma ^ ((5 * ell) / 6) := by
  rw [mem_middleEpochs] at hi
  exact ⟨Nat.pow_le_pow_right (by omega) hi.1,
    Nat.pow_le_pow_right (by omega) hi.2⟩


inductive WriterBucket (Epoch : Type*) where
  | prehistory
  | epoch (i : Epoch)
  deriving DecidableEq, Repr

section ProbeBuckets

variable {Occurrence Epoch : Type*} [DecidableEq Epoch]

def epochOccurrences (probes : Finset Occurrence)
    (lastWriter : Occurrence → WriterBucket Epoch) (i : Epoch) : Finset Occurrence :=
  probes.filter fun o => lastWriter o = .epoch i

def prehistoryOccurrences (probes : Finset Occurrence)
    (lastWriter : Occurrence → WriterBucket Epoch) : Finset Occurrence :=
  probes.filter fun o => lastWriter o = .prehistory

@[simp] theorem mem_epochOccurrences {probes : Finset Occurrence}
    {lastWriter : Occurrence → WriterBucket Epoch} {i : Epoch} {o : Occurrence} :
    o ∈ epochOccurrences probes lastWriter i ↔
      o ∈ probes ∧ lastWriter o = .epoch i := by
  simp [epochOccurrences]

@[simp] theorem mem_prehistoryOccurrences {probes : Finset Occurrence}
    {lastWriter : Occurrence → WriterBucket Epoch} {o : Occurrence} :
    o ∈ prehistoryOccurrences probes lastWriter ↔
      o ∈ probes ∧ lastWriter o = .prehistory := by
  simp [prehistoryOccurrences]

theorem epochOccurrences_disjoint {probes : Finset Occurrence}
    {lastWriter : Occurrence → WriterBucket Epoch} {i j : Epoch} (hij : i ≠ j) :
    Disjoint (epochOccurrences probes lastWriter i)
      (epochOccurrences probes lastWriter j) := by
  classical
  rw [Finset.disjoint_left]
  intro o hoi hoj
  simp only [mem_epochOccurrences] at hoi hoj
  exact hij (WriterBucket.epoch.inj (hoi.2.symm.trans hoj.2))

theorem prehistory_disjoint_epoch {probes : Finset Occurrence}
    {lastWriter : Occurrence → WriterBucket Epoch} {i : Epoch} :
    Disjoint (prehistoryOccurrences probes lastWriter)
      (epochOccurrences probes lastWriter i) := by
  classical
  rw [Finset.disjoint_left]
  intro o hoh hoi
  simp only [mem_prehistoryOccurrences] at hoh
  simp only [mem_epochOccurrences] at hoi
  cases hoh.2.symm.trans hoi.2

theorem sum_epochOccurrences_card_le (probes : Finset Occurrence)
    (lastWriter : Occurrence → WriterBucket Epoch) (epochs : Finset Epoch) :
    (∑ i ∈ epochs, (epochOccurrences probes lastWriter i).card) ≤ probes.card := by
  classical
  calc
    (∑ i ∈ epochs, (epochOccurrences probes lastWriter i).card) =
        (epochs.biUnion fun i => epochOccurrences probes lastWriter i).card := by
          symm
          apply Finset.card_biUnion
          intro i hi j hj hij
          exact epochOccurrences_disjoint hij
    _ ≤ probes.card := by
      apply Finset.card_le_card
      intro o ho
      simp only [Finset.mem_biUnion] at ho
      obtain ⟨i, hi, hoi⟩ := ho
      exact (mem_epochOccurrences.mp hoi).1

omit [DecidableEq Epoch] in
theorem exists_cheap_epoch {epochs : Finset Epoch} (hne : epochs.Nonempty)
    (charge : Epoch → ℕ) (total : ℕ)
    (hsum : (∑ i ∈ epochs, charge i) ≤ total) :
    ∃ i ∈ epochs, charge i * epochs.card ≤ total := by
  by_contra h
  push Not at h
  have hlt : (∑ _i ∈ epochs, total) <
      ∑ i ∈ epochs, charge i * epochs.card := by
    exact Finset.sum_lt_sum_of_nonempty hne fun i hi => h i hi
  have hlt' : total * epochs.card <
      (∑ i ∈ epochs, charge i) * epochs.card := by
    calc
      total * epochs.card = ∑ _i ∈ epochs, total := by
        simp [Nat.mul_comm]
      _ < ∑ i ∈ epochs, charge i * epochs.card := hlt
      _ = (∑ i ∈ epochs, charge i) * epochs.card := by
        symm
        exact Finset.sum_mul epochs charge epochs.card
  have hle : (∑ i ∈ epochs, charge i) * epochs.card ≤
      total * epochs.card := Nat.mul_le_mul_right epochs.card hsum
  exact (Nat.not_lt_of_ge hle) hlt'

theorem exists_cheap_chronogram_epoch (probes : Finset Occurrence)
    (lastWriter : Occurrence → WriterBucket Epoch) (epochs : Finset Epoch)
    (hne : epochs.Nonempty) :
    ∃ i ∈ epochs,
      (epochOccurrences probes lastWriter i).card * epochs.card ≤ probes.card := by
  exact exists_cheap_epoch hne
    (fun i => (epochOccurrences probes lastWriter i).card) probes.card
    (sum_epochOccurrences_card_le probes lastWriter epochs)

theorem exists_cheap_epoch_on_average {Sample : Type*}
    (samples : Finset Sample) (probes : Sample → Finset Occurrence)
    (lastWriter : Sample → Occurrence → WriterBucket Epoch)
    (epochs : Finset Epoch) (hne : epochs.Nonempty) :
    ∃ i ∈ epochs,
      (∑ s ∈ samples,
          (epochOccurrences (probes s) (lastWriter s) i).card) * epochs.card ≤
        ∑ s ∈ samples, (probes s).card := by
  apply exists_cheap_epoch hne
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun s hs =>
    sum_epochOccurrences_card_le (probes s) (lastWriter s) epochs

end ProbeBuckets


section ContextFixing

variable {Context : Type*} [DecidableEq Context]

def conditionalLoad {Query Update : Type*} (queries : Finset Query)
    (updates : Finset Update) (load : Context → Query → Update → ℕ)
    (r : Context) : ℕ :=
  ∑ q ∈ queries, ∑ y ∈ updates, load r q y

omit [DecidableEq Context] in
theorem sum_conditionalLoad {Query Update : Type*} (contexts : Finset Context)
    (queries : Finset Query) (updates : Finset Update)
    (load : Context → Query → Update → ℕ) :
    (∑ r ∈ contexts, conditionalLoad queries updates load r) =
      ∑ r ∈ contexts, ∑ q ∈ queries, ∑ y ∈ updates, load r q y := by
  rfl

def timeGood (contexts : Finset Context) (conditional : Context → ℕ) : Finset Context :=
  contexts.filter fun r => contexts.card * conditional r ≤
    4 * ∑ r' ∈ contexts, conditional r'

omit [DecidableEq Context] in
theorem three_quarters_timeGood (contexts : Finset Context)
    (conditional : Context → ℕ) :
    3 * contexts.card ≤ 4 * (timeGood contexts conditional).card := by
  classical
  let total := ∑ r ∈ contexts, conditional r
  let bad := contexts.filter fun r =>
    4 * total < contexts.card * conditional r
  have hsplit : (timeGood contexts conditional).card + bad.card = contexts.card := by
    simpa [timeGood, total, bad, Nat.not_le]
      using Finset.card_filter_add_card_filter_not
        (s := contexts)
        (fun r => contexts.card * conditional r ≤ 4 * total)
  by_cases htotal : total = 0
  · have hzero : ∀ r ∈ contexts, conditional r = 0 := by
      simpa [total] using
        (Finset.sum_eq_zero_iff.mp (show (∑ r ∈ contexts, conditional r) = 0 from htotal))
    have hgood : timeGood contexts conditional = contexts := by
      apply Finset.filter_eq_self.mpr
      intro r hr
      simp [hzero r hr, htotal, total]
    rw [hgood]
    omega
  · have htotal_pos : 0 < total := Nat.pos_of_ne_zero htotal
    by_cases hbad_empty : bad = ∅
    · rw [hbad_empty] at hsplit
      simp only [Finset.card_empty, add_zero] at hsplit
      omega
    · have hbad_nonempty : bad.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hbad_empty
      have hpoint : ∀ r ∈ bad,
          4 * total < contexts.card * conditional r := by
        intro r hr
        exact (Finset.mem_filter.mp hr).2
      have hsum_bad : bad.card * (4 * total) <
          ∑ r ∈ bad, contexts.card * conditional r := by
        simpa [Finset.sum_const_nat, Nat.mul_comm] using
          Finset.sum_lt_sum_of_nonempty hbad_nonempty hpoint
      have hbad_subset : bad ⊆ contexts :=
        fun r hr => (Finset.mem_filter.mp hr).1
      have hsum_le : (∑ r ∈ bad, conditional r) ≤ total := by
        exact Finset.sum_le_sum_of_subset hbad_subset
      have hscaled_le : (∑ r ∈ bad, contexts.card * conditional r) ≤
          contexts.card * total := by
        simpa only [Finset.mul_sum] using Nat.mul_le_mul_left contexts.card hsum_le
      have hprod : (4 * bad.card) * total < contexts.card * total := by
        calc
          (4 * bad.card) * total = bad.card * (4 * total) := by
            simp [Nat.mul_assoc, Nat.mul_comm]
          _ < ∑ r ∈ bad, contexts.card * conditional r := hsum_bad
          _ ≤ contexts.card * total := hscaled_le
      have hbad_lt : 4 * bad.card < contexts.card :=
        (Nat.mul_lt_mul_right htotal_pos).mp hprod
      omega

theorem simultaneousGood (contexts time matrix : Finset Context)
    (htime_sub : time ⊆ contexts) (_hmatrix_sub : matrix ⊆ contexts)
    (htime : 3 * contexts.card ≤ 4 * time.card)
    (hfail : 4 * (contexts \ matrix).card < contexts.card) :
    (time ∩ matrix).Nonempty := by
  classical
  by_contra hnone
  have hinter : time ∩ matrix = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
  have htime_fail : time ⊆ contexts \ matrix := by
    intro r hr
    have hrc : r ∈ contexts := htime_sub hr
    have hrm : r ∉ matrix := by
      intro hm
      have hempty : r ∈ (∅ : Finset Context) := by
        rw [← hinter]
        exact Finset.mem_inter.mpr ⟨hr, hm⟩
      exact (Finset.ne_empty_of_mem hempty) rfl
    exact Finset.mem_sdiff.mpr ⟨hrc, hrm⟩
  have hcard : time.card ≤ (contexts \ matrix).card :=
    Finset.card_le_card htime_fail
  have hscaled : 4 * time.card ≤ 4 * (contexts \ matrix).card :=
    Nat.mul_le_mul_left 4 hcard
  have : 4 * time.card < contexts.card := hscaled.trans_lt hfail
  omega

theorem exists_time_and_matrix_good (contexts matrixGood : Finset Context)
    (conditional : Context → ℕ) (hmatrix : matrixGood ⊆ contexts)
    (hfail : 4 * (contexts \ matrixGood).card < contexts.card) :
    ∃ r ∈ contexts,
      contexts.card * conditional r ≤
        4 * ∑ r' ∈ contexts, conditional r' ∧
      r ∈ matrixGood := by
  have hboth := simultaneousGood contexts (timeGood contexts conditional) matrixGood
    (Finset.filter_subset _ _) hmatrix
    (three_quarters_timeGood contexts conditional) hfail
  obtain ⟨r, hr⟩ := hboth
  rcases Finset.mem_inter.mp hr with ⟨hrt, hrm⟩
  rcases Finset.mem_filter.mp hrt with ⟨hrc, hbound⟩
  exact ⟨r, hrc, hbound, hrm⟩

theorem exists_good_context_for_load {Query Update : Type*}
    (contexts matrixGood : Finset Context) (queries : Finset Query)
    (updates : Finset Update) (load : Context → Query → Update → ℕ)
    (hmatrix : matrixGood ⊆ contexts)
    (hfail : 4 * (contexts \ matrixGood).card < contexts.card) :
    ∃ r ∈ contexts,
      contexts.card * conditionalLoad queries updates load r ≤
        4 * ∑ r' ∈ contexts, ∑ q ∈ queries, ∑ y ∈ updates, load r' q y ∧
      r ∈ matrixGood := by
  simpa only [sum_conditionalLoad] using
    exists_time_and_matrix_good contexts matrixGood
      (conditionalLoad queries updates load) hmatrix hfail

end ContextFixing


section StaticCache

variable {Cell Value Input : Type*} [DecidableEq Cell]

structure Write (Cell Value : Type*) where
  cell : Cell
  value : Value

abbrev Memory (Cell Value : Type*) := Cell → Value

def runWrites (base : Memory Cell Value) : List (Write Cell Value) → Memory Cell Value
  | [] => base
  | w :: ws => runWrites (Function.update base w.cell w.value) ws

def writtenCells (ws : List (Write Cell Value)) : Finset Cell :=
  (ws.map Write.cell).toFinset

@[simp] theorem mem_writtenCells {ws : List (Write Cell Value)} {c : Cell} :
    c ∈ writtenCells ws ↔ ∃ w ∈ ws, w.cell = c := by
  simp [writtenCells]

theorem writtenCells_card_le_length (ws : List (Write Cell Value)) :
    (writtenCells ws).card ≤ ws.length := by
  simpa [writtenCells] using List.toFinset_card_le (ws.map Write.cell)

@[simp] theorem runWrites_nil (base : Memory Cell Value) : runWrites base [] = base := rfl

theorem runWrites_append (base : Memory Cell Value)
    (xs ys : List (Write Cell Value)) :
    runWrites base (xs ++ ys) = runWrites (runWrites base xs) ys := by
  induction xs generalizing base with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, runWrites]
      exact ih (Function.update base x.cell x.value)

def afterTarget (base : Memory Cell Value)
    (targetWrites : Input → List (Write Cell Value)) (y : Input) : Memory Cell Value :=
  runWrites base (targetWrites y)

def finalMemory (base : Memory Cell Value)
    (targetWrites recentWrites : Input → List (Write Cell Value))
    (y : Input) : Memory Cell Value :=
  runWrites (afterTarget base targetWrites y) (recentWrites y)

theorem runWrites_eq_of_not_mem (base : Memory Cell Value)
    {ws : List (Write Cell Value)} {c : Cell} (hc : c ∉ writtenCells ws) :
    runWrites base ws c = base c := by
  induction ws generalizing base with
  | nil => rfl
  | cons w ws ih =>
      have hc_head : w.cell ≠ c := by
        intro h
        apply hc
        simp [writtenCells, h]
      have hc_tail : c ∉ writtenCells ws := by
        intro h
        apply hc
        rcases mem_writtenCells.mp h with ⟨u, hu, huc⟩
        exact mem_writtenCells.mpr ⟨u, by simp [hu], huc⟩
      simp only [runWrites]
      rw [ih (Function.update base w.cell w.value) hc_tail]
      simp [Function.update, Ne.symm hc_head]

def shadowCache (afterTarget : Memory Cell Value)
    (recent : List (Write Cell Value)) (c : Cell) : Option Value :=
  if c ∈ writtenCells recent then some (runWrites afterTarget recent c) else none

def cachedRead (afterTarget : Memory Cell Value)
    (recent : List (Write Cell Value)) (c : Cell) : Value :=
  match shadowCache afterTarget recent c with
  | some v => v
  | none => afterTarget c

theorem cachedRead_eq_runWrites (afterTarget : Memory Cell Value)
    (recent : List (Write Cell Value)) (c : Cell) :
    cachedRead afterTarget recent c = runWrites afterTarget recent c := by
  by_cases hc : c ∈ writtenCells recent
  · simp [cachedRead, shadowCache, hc]
  · simp [cachedRead, shadowCache, hc, runWrites_eq_of_not_mem afterTarget hc]

theorem cached_static_read_correct (base : Memory Cell Value)
    (targetWrites recentWrites : Input → List (Write Cell Value))
    (y : Input) (c : Cell) :
    cachedRead (afterTarget base targetWrites y) (recentWrites y) c =
      finalMemory base targetWrites recentWrites y c := by
  exact cachedRead_eq_runWrites _ _ _

inductive StaticBucket where
  | prehistory
  | target
  | recent
  deriving DecidableEq, Repr

def staticLastWriter (target recent : Finset Cell) (c : Cell) : StaticBucket :=
  if c ∈ recent then .recent else if c ∈ target then .target else .prehistory

@[simp] theorem staticLastWriter_eq_recent {target recent : Finset Cell} {c : Cell} :
    staticLastWriter target recent c = .recent ↔ c ∈ recent := by
  by_cases hr : c ∈ recent <;> by_cases ht : c ∈ target <;>
    simp [staticLastWriter, hr, ht]

@[simp] theorem staticLastWriter_eq_target {target recent : Finset Cell} {c : Cell} :
    staticLastWriter target recent c = .target ↔ c ∈ target ∧ c ∉ recent := by
  by_cases hr : c ∈ recent <;> by_cases ht : c ∈ target <;>
    simp [staticLastWriter, hr, ht]

@[simp] theorem staticLastWriter_eq_prehistory {target recent : Finset Cell} {c : Cell} :
    staticLastWriter target recent c = .prehistory ↔
      c ∉ target ∧ c ∉ recent := by
  by_cases hr : c ∈ recent <;> by_cases ht : c ∈ target <;>
    simp [staticLastWriter, hr, ht]

theorem target_iff_lastWriter_target
    (afterTarget : Memory Cell Value) (recentWrites : List (Write Cell Value))
    (target : Finset Cell) (c : Cell) :
    (c ∈ target ∧ shadowCache afterTarget recentWrites c = none) ↔
      staticLastWriter target (writtenCells recentWrites) c = .target := by
  simp [shadowCache]

section ProbeTrace

variable {Occurrence : Type*}

def paidTargetOccurrences (probes : Finset Occurrence)
    (address : Occurrence → Cell) (afterTarget : Memory Cell Value)
    (recentWrites : List (Write Cell Value)) (target : Finset Cell) :
    Finset Occurrence :=
  probes.filter fun o =>
    address o ∈ target ∧ shadowCache afterTarget recentWrites (address o) = none

def targetWriterOccurrences (probes : Finset Occurrence)
    (address : Occurrence → Cell) (recentWrites : List (Write Cell Value))
    (target : Finset Cell) : Finset Occurrence :=
  probes.filter fun o =>
    staticLastWriter target (writtenCells recentWrites) (address o) = .target

theorem paidTargetOccurrences_eq_targetWriterOccurrences
    (probes : Finset Occurrence) (address : Occurrence → Cell)
    (afterTarget : Memory Cell Value) (recentWrites : List (Write Cell Value))
    (target : Finset Cell) :
    paidTargetOccurrences probes address afterTarget recentWrites target =
      targetWriterOccurrences probes address recentWrites target := by
  ext o
  simp only [paidTargetOccurrences, targetWriterOccurrences, Finset.mem_filter]
  rw [target_iff_lastWriter_target]

theorem paidTargetOccurrences_card_eq
    (probes : Finset Occurrence) (address : Occurrence → Cell)
    (afterTarget : Memory Cell Value) (recentWrites : List (Write Cell Value))
    (target : Finset Cell) :
    (paidTargetOccurrences probes address afterTarget recentWrites target).card =
      (targetWriterOccurrences probes address recentWrites target).card := by
  rw [paidTargetOccurrences_eq_targetWriterOccurrences]

end ProbeTrace

theorem target_cells_bound (targetWrites : List (Write Cell Value)) (d tu : ℕ)
    (hprobes : targetWrites.length ≤ tu * d) :
    (writtenCells targetWrites).card ≤ tu * d :=
  (writtenCells_card_le_length targetWrites).trans hprobes

theorem shadow_cache_entries_bound (recentWrites : List (Write Cell Value))
    (bound : ℕ) (hprobes : recentWrites.length ≤ bound) :
    (writtenCells recentWrites).card ≤ bound :=
  (writtenCells_card_le_length recentWrites).trans hprobes

theorem recent_cache_geometric_bound {Epoch : Type*}
    (epochs : Finset Epoch) (writes : Epoch → List (Write Cell Value))
    (tu gamma : ℕ) (power : Epoch → ℕ)
    (hwrite : ∀ j ∈ epochs, (writes j).length ≤ tu * gamma ^ power j) :
    (epochs.biUnion fun j => writtenCells (writes j)).card ≤
      ∑ j ∈ epochs, tu * gamma ^ power j := by
  classical
  calc
    (epochs.biUnion fun j => writtenCells (writes j)).card ≤
        ∑ j ∈ epochs, (writtenCells (writes j)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ j ∈ epochs, tu * gamma ^ power j := by
      exact Finset.sum_le_sum fun j hj =>
        (writtenCells_card_le_length (writes j)).trans (hwrite j hj)

end StaticCache

end PegSeparation.LowerBound.Chronogram
