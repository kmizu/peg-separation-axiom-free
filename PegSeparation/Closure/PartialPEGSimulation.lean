import PegSeparation.Closure.PartialPEGBasic

/-!
# The translated grammar simulates the `PartialPEG` grammar

`sim`: whenever `g` derives an outcome for a subterm `e` of its rules (or a nonterminal) on an
input `v.map toChar`, the translation `toTotal e` evaluates on `v` to the corresponding result
(`Rel`), and the consuming translation `trP e` evaluates on `v` to failure unless `e` succeeded
by consuming input, in which case it gives the same rest (`RelP`). Proved by induction on the
derivation.
-/

set_option linter.unusedSectionVars false

namespace PegSeparation.Closure.PartialPEG

open PegSeparation PegSeparation.PegGrammar

section Sim

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
  {toChar : Terminal → Char} {g : Grammar}

/-- Correspondence of outcomes for `toTotal`. -/
def Rel (toChar : Terminal → Char) : Outcome → ParseResult Terminal → Prop
  | .fail, r => r = .failure
  | .ok _ rest, r => ∃ u, rest = u.map toChar ∧ r = .success u

/-- Correspondence of outcomes for `trP` on input `v`. -/
def RelP (toChar : Terminal → Char) : Outcome → List Terminal → ParseResult Terminal → Prop
  | .fail, _, r => r = .failure
  | .ok _ rest, v, r =>
      (rest = v.map toChar ∧ r = .failure) ∨ ∃ u, rest = u.map toChar ∧ u ≠ v ∧ r = .success u

/-- The expressions the simulation is about. -/
def SubGood (g : Grammar) (e : PExp) : Prop := e ∈ allSubs g ∨ ∃ i, e = .nt i

/-- The simulation statement. -/
def Sim (toChar : Terminal → Char) (g : Grammar) (e : PExp) (x : List Char) (o : Outcome) :
    Prop :=
  ∀ v : List Terminal, x = v.map toChar →
    (∃ r, (newGrammar toChar g).Evaluates (toTotal toChar g e) v r ∧ Rel toChar o r) ∧
    (∃ r, (newGrammar toChar g).Evaluates (trP toChar g e) v r ∧ RelP toChar o v r)

theorem good_sub {x y : PExp} (hx : SubGood g x) (hnt : ∀ i, x ≠ .nt i) (hy : y ∈ subterms x) :
    SubGood g y := by
  rcases hx with hx | ⟨i, rfl⟩
  · exact Or.inl (mem_allSubs_of_sub hx hy)
  · exact absurd rfl (hnt i)

theorem starCons_ne (t ts : PTree) : PTree.starCons t ts ≠ ts := by
  intro h
  have := congrArg sizeOf h
  simp only [PTree.starCons.sizeOf_spec] at this
  omega

theorem map_inj (hinj : Function.Injective toChar) {u v : List Terminal}
    (h : u.map toChar = v.map toChar) : u = v :=
  List.map_injective_iff.mpr hinj h

/-- `Z e`, the "succeeds without consuming" test used by `trP` of a sequence. -/
theorem eval_Z {a : PExp} {v : List Terminal}
    (P : (newGrammar toChar g).Evaluates (trP toChar g a) v .failure)
    (E : (newGrammar toChar g).Evaluates (toTotal toChar g a) v (.success v)) :
    (newGrammar toChar g).Evaluates
      (.sequence (.notPredicate (trP toChar g a)) (.andPredicate (toTotal toChar g a))) v
      (.success v) :=
  .sequenceSuccess (.notSuccess P) (.andSuccess E)

theorem sim (hinj : Function.Injective toChar) {e : PExp} {x : List Char} {o : Outcome}
    (D : Derives g e x o) : SubGood g e → Sim toChar g e x o := by
  induction D with
  | eps input =>
      intro _ v hx
      exact ⟨⟨_, .empty v, v, hx, rfl⟩, ⟨_, .failure v, Or.inl ⟨hx, rfl⟩⟩⟩
  | anyOk c rest =>
      intro _ v hx
      obtain ⟨t, u, rfl, -, hu⟩ := List.map_eq_cons_iff.mp hx.symm
      have E := eval_choiceOf_cons (G := newGrammar toChar g) (univList (Terminal := Terminal)) t u
      simp only [univList, Finset.mem_toList, Finset.mem_univ, if_true] at E
      exact ⟨⟨_, E, u, hu.symm, rfl⟩,
        ⟨_, E, Or.inr ⟨u, hu.symm, (List.cons_ne_self t u).symm, rfl⟩⟩⟩
  | anyFail =>
      intro _ v hx
      obtain rfl := List.map_eq_nil_iff.mp hx.symm
      exact ⟨⟨_, eval_choiceOf_nil _, rfl⟩, ⟨_, eval_choiceOf_nil _, rfl⟩⟩
  | chrOk c d rest h =>
      intro _ v hx
      obtain ⟨t, u, rfl, htd, hu⟩ := List.map_eq_cons_iff.mp hx.symm
      rw [beqChar_iff] at h
      have hp : pre toChar c = some t := (pre_eq_some hinj).mpr (htd.trans h.symm)
      have E := eval_terminal_cons (G := newGrammar toChar g) t t u
      simp only [if_true] at E
      simp only [toTotal, trP, hp]
      exact ⟨⟨_, E, u, hu.symm, rfl⟩,
        ⟨_, E, Or.inr ⟨u, hu.symm, (List.cons_ne_self t u).symm, rfl⟩⟩⟩
  | chrFail c d rest h =>
      intro _ v hx
      obtain ⟨t, u, rfl, htd, hu⟩ := List.map_eq_cons_iff.mp hx.symm
      have hcd : c ≠ d := fun e => by rw [← beqChar_iff] at e; rw [e] at h; simp at h
      simp only [toTotal, trP]
      cases hp : pre toChar c with
      | none => exact ⟨⟨_, .failure _, rfl⟩, ⟨_, .failure _, rfl⟩⟩
      | some t' =>
          have htc := (pre_eq_some hinj).mp hp
          have hne : t ≠ t' := by rintro rfl; exact hcd (htc.symm.trans htd)
          have E := eval_terminal_cons (G := newGrammar toChar g) t' t u
          simp only [hne, if_false] at E
          exact ⟨⟨_, E, rfl⟩, ⟨_, E, rfl⟩⟩
  | chrEmpty c =>
      intro _ v hx
      obtain rfl := List.map_eq_nil_iff.mp hx.symm
      simp only [toTotal, trP]
      cases pre toChar c with
      | none => exact ⟨⟨_, .failure _, rfl⟩, ⟨_, .failure _, rfl⟩⟩
      | some t => exact ⟨⟨_, eval_terminal_nil t, rfl⟩, ⟨_, eval_terminal_nil t, rfl⟩⟩
  | rangeOk lo hi d rest h =>
      intro _ v hx
      obtain ⟨t, u, rfl, htd, hu⟩ := List.map_eq_cons_iff.mp hx.symm
      have hm : t ∈ rangeList toChar lo hi := by
        simp [rangeList, univList, htd, h]
      have E := eval_choiceOf_cons (G := newGrammar toChar g) (rangeList toChar lo hi) t u
      simp only [hm, if_true] at E
      exact ⟨⟨_, E, u, hu.symm, rfl⟩,
        ⟨_, E, Or.inr ⟨u, hu.symm, (List.cons_ne_self t u).symm, rfl⟩⟩⟩
  | rangeFail lo hi d rest h =>
      intro _ v hx
      obtain ⟨t, u, rfl, htd, hu⟩ := List.map_eq_cons_iff.mp hx.symm
      have hm : t ∉ rangeList toChar lo hi := by
        simp [rangeList, univList, htd, h]
      have E := eval_choiceOf_cons (G := newGrammar toChar g) (rangeList toChar lo hi) t u
      simp only [hm, if_false] at E
      exact ⟨⟨_, E, rfl⟩, ⟨_, E, rfl⟩⟩
  | rangeEmpty lo hi =>
      intro _ v hx
      obtain rfl := List.map_eq_nil_iff.mp hx.symm
      exact ⟨⟨_, eval_choiceOf_nil _, rfl⟩, ⟨_, eval_choiceOf_nil _, rfl⟩⟩
  | litOk s input rest h =>
      intro _ v hx
      subst hx
      obtain ⟨u, hu, E⟩ := eval_litE_ok (G := newGrammar toChar g) hinj s v rest h
      have happ := stripPrefix?_eq_some h
      refine ⟨⟨_, E, u, hu, rfl⟩, ?_⟩
      simp only [trP]
      split
      · rename_i hs
        subst hs
        exact ⟨_, .failure _, Or.inl ⟨by simpa using happ.symm, rfl⟩⟩
      · rename_i hs
        refine ⟨_, E, Or.inr ⟨u, hu, ?_, rfl⟩⟩
        rintro rfl
        have := congrArg List.length happ
        rw [hu, List.length_append] at this
        exact hs (List.length_eq_zero_iff.mp (by omega))
  | litFail s input h =>
      intro _ v hx
      subst hx
      have E := eval_litE_fail (G := newGrammar toChar g) hinj s v h
      refine ⟨⟨_, E, rfl⟩, ?_⟩
      simp only [trP]
      split
      · rename_i hs; subst hs; simp [stripPrefix?] at h
      · exact ⟨_, E, rfl⟩
  | ntOk i e input rest t hr hd ih =>
      intro _ v hx
      obtain ⟨hi, he⟩ := ruleAt_eq_some hr
      obtain ⟨⟨r, E, R⟩, ⟨p, P, RP⟩⟩ :=
        ih (Or.inl (he ▸ rule_mem_allSubs hi)) v hx
      simp only [toTotal, trP, hi, if_true]
      refine ⟨⟨r, ntE_eval toChar g (lt_ntCount_of_lt g hi) ?_, R⟩,
        ⟨p, ntE_eval toChar g (add_lt_ntCount_of_lt g hi) ?_, RP⟩⟩
      · rw [newRule_lt toChar g hi, he]; exact E
      · rw [newRule_add toChar g hi, he]; exact P
  | ntFail i e input hr hd ih =>
      intro _ v hx
      obtain ⟨hi, he⟩ := ruleAt_eq_some hr
      obtain ⟨⟨r, E, R⟩, ⟨p, P, RP⟩⟩ :=
        ih (Or.inl (he ▸ rule_mem_allSubs hi)) v hx
      simp only [toTotal, trP, hi, if_true]
      refine ⟨⟨r, ntE_eval toChar g (lt_ntCount_of_lt g hi) ?_, R⟩,
        ⟨p, ntE_eval toChar g (add_lt_ntCount_of_lt g hi) ?_, RP⟩⟩
      · rw [newRule_lt toChar g hi, he]; exact E
      · rw [newRule_add toChar g hi, he]; exact P
  | ntMissing i input hr =>
      intro _ v _
      have hi := ruleAt_eq_none hr
      simp only [toTotal, trP, hi, if_false]
      exact ⟨⟨_, .failure _, rfl⟩, ⟨_, .failure _, rfl⟩⟩
  | seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
      intro hg v hx
      have hnt : ∀ i, PExp.seq e₁ e₂ ≠ .nt i := fun _ h => by cases h
      have g₁ := good_sub (y := e₁) hg hnt (by simp [subterms, mem_subterms_self])
      have g₂ := good_sub (y := e₂) hg hnt (by simp [subterms, mem_subterms_self])
      obtain ⟨⟨r₁, E₁, R₁⟩, ⟨p₁, P₁, RP₁⟩⟩ := ih₁ g₁ v hx
      obtain ⟨u₁, hu₁, rfl⟩ := R₁
      obtain ⟨⟨r₂, E₂, R₂⟩, ⟨p₂, P₂, RP₂⟩⟩ := ih₂ g₂ u₁ hu₁
      obtain ⟨u₂, hu₂, rfl⟩ := R₂
      refine ⟨⟨_, .sequenceSuccess E₁ E₂, u₂, hu₂, rfl⟩, ?_⟩
      rcases RP₁ with ⟨hv, rfl⟩ | ⟨u₁', hu₁', hne, rfl⟩
      · obtain rfl := map_inj hinj (hu₁.symm.trans hv)
        exact ⟨p₂, .choiceRight (.sequenceFailure P₁) (.sequenceSuccess (eval_Z P₁ E₁) P₂), RP₂⟩
      · obtain rfl := map_inj hinj (hu₁'.symm.trans hu₁)
        refine ⟨_, .choiceLeft (.sequenceSuccess P₁ E₂), Or.inr ⟨u₂, hu₂, ?_, rfl⟩⟩
        rintro rfl
        have := eq_of_suffix_squeeze (derives_rest_suffix h₂ rfl) (derives_rest_suffix h₁ rfl)
          (hu₂.trans hx.symm)
        exact hne (map_inj hinj (hu₁.symm.trans (this.trans hx)))
  | seqFail₁ e₁ e₂ input h₁ ih₁ =>
      intro hg v hx
      have hnt : ∀ i, PExp.seq e₁ e₂ ≠ .nt i := fun _ h => by cases h
      have g₁ := good_sub (y := e₁) hg hnt (by simp [subterms, mem_subterms_self])
      obtain ⟨⟨r₁, E₁, rfl⟩, ⟨p₁, P₁, rfl⟩⟩ := ih₁ g₁ v hx
      exact ⟨⟨_, .sequenceFailure E₁, rfl⟩, ⟨_, .choiceRight (.sequenceFailure P₁)
        (.sequenceFailure (.sequenceSuccess (.notSuccess P₁) (.andFailure E₁))), rfl⟩⟩
  | seqFail₂ e₁ e₂ input rest₁ t₁ h₁ h₂ ih₁ ih₂ =>
      intro hg v hx
      have hnt : ∀ i, PExp.seq e₁ e₂ ≠ .nt i := fun _ h => by cases h
      have g₁ := good_sub (y := e₁) hg hnt (by simp [subterms, mem_subterms_self])
      have g₂ := good_sub (y := e₂) hg hnt (by simp [subterms, mem_subterms_self])
      obtain ⟨⟨r₁, E₁, R₁⟩, ⟨p₁, P₁, RP₁⟩⟩ := ih₁ g₁ v hx
      obtain ⟨u₁, hu₁, rfl⟩ := R₁
      obtain ⟨⟨r₂, E₂, rfl⟩, ⟨p₂, P₂, rfl⟩⟩ := ih₂ g₂ u₁ hu₁
      refine ⟨⟨_, .sequenceSuccess E₁ E₂, rfl⟩, ?_⟩
      rcases RP₁ with ⟨hv, rfl⟩ | ⟨u₁', hu₁', hne, rfl⟩
      · obtain rfl := map_inj hinj (hu₁.symm.trans hv)
        exact ⟨_, .choiceRight (.sequenceFailure P₁) (.sequenceSuccess (eval_Z P₁ E₁) P₂), rfl⟩
      · obtain rfl := map_inj hinj (hu₁'.symm.trans hu₁)
        exact ⟨_, .choiceRight (.sequenceSuccess P₁ E₂)
          (.sequenceFailure (.sequenceFailure (.notFailure P₁))), rfl⟩
  | altL e₁ e₂ input rest t h ih =>
      intro hg v hx
      have hnt : ∀ i, PExp.alt e₁ e₂ ≠ .nt i := fun _ h => by cases h
      have g₁ := good_sub (y := e₁) hg hnt (by simp [subterms, mem_subterms_self])
      obtain ⟨⟨r₁, E₁, R₁⟩, ⟨p₁, P₁, RP₁⟩⟩ := ih g₁ v hx
      obtain ⟨u₁, hu₁, rfl⟩ := R₁
      refine ⟨⟨_, .choiceLeft E₁, u₁, hu₁, rfl⟩, ?_⟩
      rcases RP₁ with ⟨hv, rfl⟩ | ⟨u₁', hu₁', hne, rfl⟩
      · exact ⟨_, .choiceRight P₁ (.sequenceFailure (.notFailure E₁)), Or.inl ⟨hv, rfl⟩⟩
      · exact ⟨_, .choiceLeft P₁, Or.inr ⟨u₁', hu₁', hne, rfl⟩⟩
  | altR e₁ e₂ input rest t h₁ h₂ ih₁ ih₂ =>
      intro hg v hx
      have hnt : ∀ i, PExp.alt e₁ e₂ ≠ .nt i := fun _ h => by cases h
      have g₁ := good_sub (y := e₁) hg hnt (by simp [subterms, mem_subterms_self])
      have g₂ := good_sub (y := e₂) hg hnt (by simp [subterms, mem_subterms_self])
      obtain ⟨⟨r₁, E₁, rfl⟩, ⟨p₁, P₁, rfl⟩⟩ := ih₁ g₁ v hx
      obtain ⟨⟨r₂, E₂, R₂⟩, ⟨p₂, P₂, RP₂⟩⟩ := ih₂ g₂ v hx
      exact ⟨⟨_, .choiceRight E₁ E₂, R₂⟩,
        ⟨_, .choiceRight P₁ (.sequenceSuccess (.notSuccess E₁) P₂), RP₂⟩⟩
  | altFail e₁ e₂ input h₁ h₂ ih₁ ih₂ =>
      intro hg v hx
      have hnt : ∀ i, PExp.alt e₁ e₂ ≠ .nt i := fun _ h => by cases h
      have g₁ := good_sub (y := e₁) hg hnt (by simp [subterms, mem_subterms_self])
      have g₂ := good_sub (y := e₂) hg hnt (by simp [subterms, mem_subterms_self])
      obtain ⟨⟨r₁, E₁, rfl⟩, ⟨p₁, P₁, rfl⟩⟩ := ih₁ g₁ v hx
      obtain ⟨⟨r₂, E₂, rfl⟩, ⟨p₂, P₂, rfl⟩⟩ := ih₂ g₂ v hx
      exact ⟨⟨_, .choiceRight E₁ E₂, rfl⟩,
        ⟨_, .choiceRight P₁ (.sequenceSuccess (.notSuccess E₁) P₂), rfl⟩⟩
  | starNil a input h ih =>
      intro hg v hx
      have hnt : ∀ i, PExp.star a ≠ .nt i := fun _ h => by cases h
      have hmem : PExp.star a ∈ allSubs g := hg.resolve_right (by rintro ⟨i, h⟩; cases h)
      have g₁ := good_sub (y := a) hg hnt (by simp [subterms, mem_subterms_self])
      obtain ⟨⟨r₁, E₁, rfl⟩, ⟨p₁, P₁, rfl⟩⟩ := ih g₁ v hx
      refine ⟨⟨_, ntE_eval toChar g (starIdx_lt g a) ?_, v, hx, rfl⟩,
        ⟨_, .sequenceFailure P₁, Or.inl ⟨hx, rfl⟩⟩⟩
      rw [newRule_starIdx toChar g hmem]
      exact .choiceRight (.sequenceFailure P₁) (.empty v)
  | starCons a input rest rest' t ts h₁ h₂ ih₁ ih₂ =>
      intro hg v hx
      have hnt : ∀ i, PExp.star a ≠ .nt i := fun _ h => by cases h
      have hmem : PExp.star a ∈ allSubs g := hg.resolve_right (by rintro ⟨i, h⟩; cases h)
      have g₁ := good_sub (y := a) hg hnt (by simp [subterms, mem_subterms_self])
      have hrest : rest ≠ input := by
        rintro rfl
        have := derives_det (Derives.starCons a rest rest rest' t ts h₁ h₂) h₂
        injection this with h
        exact starCons_ne t ts h
      obtain ⟨⟨r₁, E₁, R₁⟩, ⟨p₁, P₁, RP₁⟩⟩ := ih₁ g₁ v hx
      obtain ⟨u, hu, rfl⟩ := R₁
      obtain ⟨⟨r₂, E₂, R₂⟩, -⟩ := ih₂ hg u hu
      obtain ⟨u', hu', rfl⟩ := R₂
      rcases RP₁ with ⟨hv, -⟩ | ⟨u₁, hu₁, hne, rfl⟩
      · exact absurd (hv.trans hx.symm) hrest
      · obtain rfl := map_inj hinj (hu₁.symm.trans hu)
        refine ⟨⟨_, ntE_eval toChar g (starIdx_lt g a) ?_, u', hu', rfl⟩,
          ⟨_, .sequenceSuccess P₁ E₂, Or.inr ⟨u', hu', ?_, rfl⟩⟩⟩
        · rw [newRule_starIdx toChar g hmem]
          exact .choiceLeft (.sequenceSuccess P₁ E₂)
        · rintro rfl
          exact hrest (eq_of_suffix_squeeze (derives_rest_suffix h₂ rfl) (derives_rest_suffix h₁ rfl)
            (hu'.trans hx.symm))
  | notOk e input rest t h ih =>
      intro hg v hx
      have hnt : ∀ i, PExp.notP e ≠ .nt i := fun _ h => by cases h
      have g₁ := good_sub (y := e) hg hnt (by simp [subterms, mem_subterms_self])
      obtain ⟨⟨r₁, E₁, R₁⟩, -⟩ := ih g₁ v hx
      obtain ⟨u, -, rfl⟩ := R₁
      exact ⟨⟨_, .notFailure E₁, rfl⟩, ⟨_, .failure v, rfl⟩⟩
  | notFail e input h ih =>
      intro hg v hx
      have hnt : ∀ i, PExp.notP e ≠ .nt i := fun _ h => by cases h
      have g₁ := good_sub (y := e) hg hnt (by simp [subterms, mem_subterms_self])
      obtain ⟨⟨r₁, E₁, rfl⟩, -⟩ := ih g₁ v hx
      exact ⟨⟨_, .notSuccess E₁, v, hx, rfl⟩, ⟨_, .failure v, Or.inl ⟨hx, rfl⟩⟩⟩

end Sim

end PegSeparation.Closure.PartialPEG
