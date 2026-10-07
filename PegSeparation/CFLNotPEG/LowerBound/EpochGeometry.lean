import PegSeparation.CFLNotPEG.LowerBound.Chronogram


namespace PegSeparation.LowerBound.EpochGeometry

open PegSeparation.LowerBound.Chronogram

def epochStart (n gamma i : ℕ) : ℕ :=
  n - peeledMass gamma (i + 1)

def epochEnd (n gamma i : ℕ) : ℕ :=
  epochStart n gamma i + gamma ^ i

def prefixRange (n gamma i : ℕ) : Finset ℕ :=
  Finset.range (epochStart n gamma i)

def targetRange (n gamma i : ℕ) : Finset ℕ :=
  Finset.Ico (epochStart n gamma i) (epochEnd n gamma i)

def recentRange (n gamma i : ℕ) : Finset ℕ :=
  Finset.Ico (epochEnd n gamma i) n

theorem middleEpoch_mem_Ico {ell i : ℕ} (hell : 1 ≤ ell)
    (hi : i ∈ middleEpochs ell) :
    i ∈ Finset.Ico 1 ell := by
  simp only [mem_middleEpochs] at hi
  simp only [Finset.mem_Ico]
  omega

theorem peeledMass_succ_le_updates {n gamma ell i : ℕ}
    (hell : 1 ≤ ell) (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n) (hi : i ∈ middleEpochs ell) :
    peeledMass gamma (i + 1) ≤ n := by
  have hiIco : i ∈ Finset.Ico 1 ell := middleEpoch_mem_Ico hell hi
  have hiell : i + 1 ≤ ell := by
    have hiLess : i < ell := (Finset.mem_Ico.mp hiIco).2
    omega
  exact (peeledMass_mono gamma hiell).trans
    (peeledMass_lt_updates hgamma hpower).le

theorem epochEnd_eq_sub_peeledMass {n gamma i : ℕ} (hi : 1 ≤ i)
    (hfit : peeledMass gamma (i + 1) ≤ n) :
    epochEnd n gamma i = n - peeledMass gamma i := by
  rw [peeledMass_succ hi] at hfit
  rw [epochEnd, epochStart, peeledMass_succ hi]
  omega

theorem epochStart_add_power_le_updates {n gamma ell i : ℕ}
    (hell : 1 ≤ ell) (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n) (hi : i ∈ middleEpochs ell) :
    epochStart n gamma i + gamma ^ i ≤ n := by
  have hiIco : i ∈ Finset.Ico 1 ell := middleEpoch_mem_Ico hell hi
  have hiOne : 1 ≤ i := (Finset.mem_Ico.mp hiIco).1
  have hfit : peeledMass gamma (i + 1) ≤ n :=
    peeledMass_succ_le_updates hell hgamma hpower hi
  change epochEnd n gamma i ≤ n
  rw [epochEnd_eq_sub_peeledMass hiOne hfit]
  exact Nat.sub_le _ _

def targetEmbedding (n gamma i : ℕ)
    (hfit : epochEnd n gamma i ≤ n) : Fin (gamma ^ i) ↪ Fin n where
  toFun k := ⟨epochStart n gamma i + k.val, by
    have hk : epochStart n gamma i + k.val < epochEnd n gamma i := by
      simpa only [epochEnd] using
        Nat.add_lt_add_left k.isLt (epochStart n gamma i)
    exact hk.trans_le hfit⟩
  inj' := by
    intro a b hab
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val hab)

@[simp] theorem targetEmbedding_val (n gamma i : ℕ)
    (hfit : epochEnd n gamma i ≤ n) (k : Fin (gamma ^ i)) :
    (targetEmbedding n gamma i hfit k).val = epochStart n gamma i + k.val :=
  rfl

theorem targetEmbedding_injective (n gamma i : ℕ)
    (hfit : epochEnd n gamma i ≤ n) :
    Function.Injective (targetEmbedding n gamma i hfit) :=
  (targetEmbedding n gamma i hfit).injective

def targetImage (n gamma i : ℕ)
    (hfit : epochEnd n gamma i ≤ n) : Finset ℕ :=
  Finset.univ.image fun k : Fin (gamma ^ i) =>
    (targetEmbedding n gamma i hfit k).val

theorem targetImage_eq_targetRange (n gamma i : ℕ)
    (hfit : epochEnd n gamma i ≤ n) :
    targetImage n gamma i hfit = targetRange n gamma i := by
  ext x
  simp only [targetImage, Finset.mem_image, Finset.mem_univ, true_and,
    targetRange, Finset.mem_Ico]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨Nat.le_add_right _ _, by
      simpa only [targetEmbedding_val, epochEnd] using
        Nat.add_lt_add_left k.isLt (epochStart n gamma i)⟩
  · intro hx
    let k : Fin (gamma ^ i) := ⟨x - epochStart n gamma i, by
      rw [epochEnd] at hx
      omega⟩
    refine ⟨k, ?_⟩
    change epochStart n gamma i + (x - epochStart n gamma i) = x
    omega

theorem targetRange_disjoint_of_ne {n gamma ell i j : ℕ}
    (hell : 1 ≤ ell) (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n)
    (hi : i ∈ middleEpochs ell) (hj : j ∈ middleEpochs ell)
    (hij : i ≠ j) :
    Disjoint (targetRange n gamma i) (targetRange n gamma j) := by
  have hiIco : i ∈ Finset.Ico 1 ell := middleEpoch_mem_Ico hell hi
  have hjIco : j ∈ Finset.Ico 1 ell := middleEpoch_mem_Ico hell hj
  have hiOne : 1 ≤ i := (Finset.mem_Ico.mp hiIco).1
  have hjOne : 1 ≤ j := (Finset.mem_Ico.mp hjIco).1
  have hfitI : peeledMass gamma (i + 1) ≤ n :=
    peeledMass_succ_le_updates hell hgamma hpower hi
  have hfitJ : peeledMass gamma (j + 1) ≤ n :=
    peeledMass_succ_le_updates hell hgamma hpower hj
  rw [Finset.disjoint_left]
  intro x hxi hxj
  simp only [targetRange, Finset.mem_Ico] at hxi hxj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hmass : peeledMass gamma (i + 1) ≤ peeledMass gamma j :=
      peeledMass_mono gamma (by omega)
    have horder : epochEnd n gamma j ≤ epochStart n gamma i := by
      rw [epochEnd_eq_sub_peeledMass hjOne hfitJ, epochStart]
      omega
    omega
  · have hmass : peeledMass gamma (j + 1) ≤ peeledMass gamma i :=
      peeledMass_mono gamma (by omega)
    have horder : epochEnd n gamma i ≤ epochStart n gamma j := by
      rw [epochEnd_eq_sub_peeledMass hiOne hfitI, epochStart]
      omega
    omega

theorem targetImages_disjoint_of_ne {n gamma ell i j : ℕ}
    (hell : 1 ≤ ell) (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n)
    (hi : i ∈ middleEpochs ell) (hj : j ∈ middleEpochs ell)
    (hij : i ≠ j) :
    Disjoint
      (targetImage n gamma i
        (epochStart_add_power_le_updates hell hgamma hpower hi))
      (targetImage n gamma j
        (epochStart_add_power_le_updates hell hgamma hpower hj)) := by
  rw [targetImage_eq_targetRange, targetImage_eq_targetRange]
  exact targetRange_disjoint_of_ne hell hgamma hpower hi hj hij

@[simp] theorem card_prefixRange (n gamma i : ℕ) :
    (prefixRange n gamma i).card = epochStart n gamma i := by
  simp [prefixRange]

@[simp] theorem card_targetRange (n gamma i : ℕ) :
    (targetRange n gamma i).card = gamma ^ i := by
  simp [targetRange, epochEnd]

theorem prefix_target_recent_partition {n gamma i : ℕ}
    (hfit : epochEnd n gamma i ≤ n) :
    prefixRange n gamma i ∪ targetRange n gamma i ∪
      recentRange n gamma i = Finset.range n := by
  ext x
  simp only [prefixRange, targetRange, recentRange, Finset.mem_union,
    Finset.mem_range, Finset.mem_Ico]
  have hstart : epochStart n gamma i ≤ epochEnd n gamma i := by
    simp [epochEnd]
  omega

theorem prefix_target_disjoint (n gamma i : ℕ) :
    Disjoint (prefixRange n gamma i) (targetRange n gamma i) := by
  rw [Finset.disjoint_left]
  intro x hxPrefix hxTarget
  simp only [prefixRange, Finset.mem_range] at hxPrefix
  simp only [targetRange, Finset.mem_Ico] at hxTarget
  omega

theorem target_recent_disjoint (n gamma i : ℕ) :
    Disjoint (targetRange n gamma i) (recentRange n gamma i) := by
  rw [Finset.disjoint_left]
  intro x hxTarget hxRecent
  simp only [targetRange, recentRange, Finset.mem_Ico] at hxTarget hxRecent
  omega

theorem prefix_recent_disjoint (n gamma i : ℕ) :
    Disjoint (prefixRange n gamma i) (recentRange n gamma i) := by
  rw [Finset.disjoint_left]
  intro x hxPrefix hxRecent
  simp only [prefixRange, Finset.mem_range] at hxPrefix
  simp only [recentRange, Finset.mem_Ico] at hxRecent
  have hstartEnd : epochStart n gamma i ≤ epochEnd n gamma i := by
    simp [epochEnd]
  omega

theorem card_recentRange {n gamma i : ℕ} (hi : 1 ≤ i)
    (hfit : peeledMass gamma (i + 1) ≤ n) :
    (recentRange n gamma i).card = peeledMass gamma i := by
  have hmass : peeledMass gamma i ≤ n :=
    (peeledMass_mono gamma (by omega : i ≤ i + 1)).trans hfit
  rw [recentRange, Nat.card_Ico, epochEnd_eq_sub_peeledMass hi hfit]
  omega

theorem card_recentRange_of_middle {n gamma ell i : ℕ}
    (hell : 1 ≤ ell) (hgamma : 2 ≤ gamma)
    (hpower : gamma ^ ell ≤ n) (hi : i ∈ middleEpochs ell) :
    (recentRange n gamma i).card = peeledMass gamma i := by
  have hiOne : 1 ≤ i :=
    (Finset.mem_Ico.mp (middleEpoch_mem_Ico hell hi)).1
  exact card_recentRange hiOne
    (peeledMass_succ_le_updates hell hgamma hpower hi)

end PegSeparation.LowerBound.EpochGeometry
