import PegSeparation.Closure.PartialPEGSimulation

/-!
# From `lean4-peg` PEGs to the artifact's total PEGs

`recognizedByTotalPEG_of_partialPEG`: if every nonterminal of a `PartialPEG` grammar `g` (over
`Char`, with repetition, character classes, literals and the wildcard) terminates on every input,
then for every finite alphabet `Terminal` embedded in `Char`, the language of `g` restricted to
words over `Terminal` is recognized by a total PEG of the artifact.

The total PEG is `newGrammar toChar g` (`PartialPEGTranslate`). It is total: the translations of
the rules of `g` terminate by the simulation (`sim`) and the termination of `g`; the repetition
nonterminals `X ← trP(a) X / ε` terminate on every input by induction on its length, since `trP a`
only succeeds by consuming input (`trP_strict`). It recognizes the right language by the
simulation and determinism of evaluation.
-/

set_option linter.unusedSectionVars false

namespace PegSeparation.Closure.PartialPEG

open PegSeparation PegSeparation.PegGrammar

section Total

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
  {toChar : Terminal → Char} {g : Grammar}

/-- The translations of the rules of `g` evaluate on every input. -/
theorem rule_total (hinj : Function.Injective toChar)
    (htot : ∀ (i : Nat) (w : List Char), ∃ o, Derives g (.nt i) w o)
    {i : Nat} (hi : i < g.rules.length) (v : List Terminal) :
    (∃ r, (newGrammar toChar g).Evaluates (toTotal toChar g g.rules[i]) v r) ∧
    (∃ r, (newGrammar toChar g).Evaluates (trP toChar g g.rules[i]) v r) := by
  obtain ⟨o, D⟩ := htot i (v.map toChar)
  obtain ⟨⟨r, E, -⟩, ⟨p, P, -⟩⟩ := sim hinj D (Or.inr ⟨i, rfl⟩) v rfl
  simp only [toTotal, trP, hi, if_true] at E P
  have E' := ntE_eval_inv toChar g (lt_ntCount_of_lt g hi) E
  have P' := ntE_eval_inv toChar g (add_lt_ntCount_of_lt g hi) P
  rw [newRule_lt toChar g hi] at E'
  rw [newRule_add toChar g hi] at P'
  exact ⟨⟨r, E'⟩, ⟨p, P'⟩⟩

/-- A repetition nonterminal evaluates on every input. -/
theorem star_total {a : PExp} {j : Nat} (hj : j < ntCount g)
    (hrule : newRule toChar g ⟨j, hj⟩ =
      .orderedChoice (.sequence (trP toChar g a) (ntE g j)) .empty)
    (hP : ∀ v, ∃ r, (newGrammar toChar g).Evaluates (trP toChar g a) v r) :
    ∀ v, ∃ r, (newGrammar toChar g).Evaluates (ntE g j) v r := by
  suffices h : ∀ n (v : List Terminal), v.length = n →
      ∃ r, (newGrammar toChar g).Evaluates (ntE g j) v r from fun v => h _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro v hv
      obtain ⟨r, hr⟩ := hP v
      cases r with
      | failure =>
          refine ⟨.success v, ntE_eval toChar g hj ?_⟩
          rw [hrule]
          exact .choiceRight (.sequenceFailure hr) (.empty v)
      | success u =>
          have hs := eval_suffix hr rfl
          have hne := trP_strict toChar g hr
          have hlt : u.length < n := by
            have h1 := hs.length_le
            have h2 : u.length ≠ v.length := fun h => hne (hs.eq_of_length h)
            omega
          obtain ⟨r', hr'⟩ := ih _ hlt u rfl
          obtain ⟨r'', hr''⟩ := PartialTotalityHelpers.orderedChoice_total
            ⟨_, Evaluates.sequenceSuccess hr hr'⟩
            ⟨_, Evaluates.empty (grammar := newGrammar toChar g) v⟩
          exact ⟨r'', ntE_eval toChar g hj (by rw [hrule]; exact hr'')⟩

/-- Both translations of every expression evaluate on every input. -/
theorem tr_total (hinj : Function.Injective toChar)
    (htot : ∀ (i : Nat) (w : List Char), ∃ o, Derives g (.nt i) w o) (e : PExp) :
    ∀ v : List Terminal,
      (∃ r, (newGrammar toChar g).Evaluates (toTotal toChar g e) v r) ∧
      (∃ r, (newGrammar toChar g).Evaluates (trP toChar g e) v r) := by
  induction e with
  | eps => intro v; exact ⟨⟨_, .empty v⟩, ⟨_, .failure v⟩⟩
  | any => intro v; exact ⟨choiceOf_total _ v, choiceOf_total _ v⟩
  | chr c =>
      intro v
      simp only [toTotal, trP]
      cases pre toChar c with
      | none => exact ⟨⟨_, .failure v⟩, ⟨_, .failure v⟩⟩
      | some t => exact ⟨⟨_, .terminal t v⟩, ⟨_, .terminal t v⟩⟩
  | range lo hi => intro v; exact ⟨choiceOf_total _ v, choiceOf_total _ v⟩
  | lit s =>
      intro v
      refine ⟨litE_total s v, ?_⟩
      simp only [trP]
      split
      · exact ⟨_, .failure v⟩
      · exact litE_total s v
  | nt i =>
      intro v
      simp only [toTotal, trP]
      split
      · rename_i hi
        obtain ⟨⟨r, E⟩, ⟨p, P⟩⟩ := rule_total hinj htot hi v
        refine ⟨⟨r, ntE_eval toChar g (lt_ntCount_of_lt g hi) ?_⟩,
          ⟨p, ntE_eval toChar g (add_lt_ntCount_of_lt g hi) ?_⟩⟩
        · rw [newRule_lt toChar g hi]; exact E
        · rw [newRule_add toChar g hi]; exact P
      · exact ⟨⟨_, .failure v⟩, ⟨_, .failure v⟩⟩
  | seq a b iha ihb =>
      intro v
      refine ⟨PartialTotalityHelpers.sequence_total (iha v).1 (fun m => (ihb m).1), ?_⟩
      exact PartialTotalityHelpers.orderedChoice_total
        (PartialTotalityHelpers.sequence_total (iha v).2 (fun m => (ihb m).1))
        (PartialTotalityHelpers.sequence_total
          (PartialTotalityHelpers.sequence_total
            (PartialTotalityHelpers.notPredicate_total (iha v).2)
            (fun m => PartialTotalityHelpers.andPredicate_total (iha m).1))
          (fun m => (ihb m).2))
  | alt a b iha ihb =>
      intro v
      exact ⟨PartialTotalityHelpers.orderedChoice_total (iha v).1 (ihb v).1,
        PartialTotalityHelpers.orderedChoice_total (iha v).2
          (PartialTotalityHelpers.sequence_total
            (PartialTotalityHelpers.notPredicate_total (iha v).1) (fun m => (ihb m).2))⟩
  | star a iha =>
      have hX : ∀ v, ∃ r, (newGrammar toChar g).Evaluates (ntE g (starIdx g a)) v r := by
        by_cases hmem : PExp.star a ∈ allSubs g
        · exact star_total (starIdx_lt g a) (newRule_starIdx toChar g hmem) (fun v => (iha v).2)
        · intro v
          refine ⟨.failure, ntE_eval toChar g (starIdx_lt g a) ?_⟩
          rw [newRule_star_not_mem toChar g hmem]
          exact .failure v
      intro v
      exact ⟨hX v, PartialTotalityHelpers.sequence_total (iha v).2 hX⟩
  | notP a iha =>
      intro v
      exact ⟨PartialTotalityHelpers.notPredicate_total (iha v).1, ⟨_, .failure v⟩⟩

/-- Every nonterminal of the translated grammar evaluates on every input. -/
theorem newGrammar_nonterminal_total (hinj : Function.Injective toChar)
    (htot : ∀ (i : Nat) (w : List Char), ∃ o, Derives g (.nt i) w o)
    (j : Fin (ntCount g)) (v : List Terminal) :
    ∃ r, (newGrammar toChar g).Evaluates (.nonterminal j) v r := by
  suffices h : ∃ r, (newGrammar toChar g).Evaluates (newRule toChar g j) v r by
    obtain ⟨r, h⟩ := h
    exact ⟨r, .nonterminal h⟩
  unfold newRule
  split
  · exact (tr_total hinj htot _ v).1
  split
  · exact (tr_total hinj htot _ v).2
  split
  · rename_i h1 h2 h3
    cases hk : (allSubs g)[j.val - 2 * g.rules.length] with
    | star a =>
        have hX := star_total (g := g) (a := a) j.isLt
          (by
            unfold newRule
            simp only [h1, h2, h3, dif_neg, dif_pos, not_false_eq_true, hk]
            rfl)
          (fun v => (tr_total hinj htot a v).2) v
        obtain ⟨r, hr⟩ := hX
        exact ⟨r, by
          have := ntE_eval_inv toChar g j.isLt hr
          unfold newRule at this
          simpa only [h1, h2, h3, dif_neg, dif_pos, not_false_eq_true, hk] using this⟩
    | _ => exact ⟨_, .failure v⟩
  · exact ⟨_, .failure v⟩

theorem newGrammar_isLoffTotal (hinj : Function.Injective toChar)
    (htot : ∀ (i : Nat) (w : List Char), ∃ o, Derives g (.nt i) w o) :
    (newGrammar toChar g).IsLoffTotal :=
  PartialTotalityHelpers.loffTotal_of_nonterminal_total
    (newGrammar_nonterminal_total hinj htot)

end Total

/-- **Bridge.** A `PartialPEG` grammar whose nonterminals all terminate recognizes, on every finite
alphabet embedded in `Char`, a language recognized by a total PEG. -/
theorem recognizedByTotalPEG_of_partialPEG {Terminal : Type} [Fintype Terminal]
    [DecidableEq Terminal]
    (toChar : Terminal → Char) (hinj : Function.Injective toChar)
    (g : PartialPEG.Grammar)
    (htot : ∀ (i : Nat) (w : List Char), ∃ o, PartialPEG.Derives g (.nt i) w o) :
    PegSeparation.RecognizedByTotalPEG
      (fun v : List Terminal =>
        ∃ t, PartialPEG.Derives g (.nt g.start) (v.map toChar) (.ok t [])) := by
  refine ⟨ntCount g, newGrammar toChar g, newGrammar_isLoffTotal hinj htot, fun v => ?_⟩
  change (newGrammar toChar g).Recognizes v ↔
    ∃ t, PartialPEG.Derives g (.nt g.start) (v.map toChar) (.ok t [])
  unfold Recognizes
  by_cases hs : g.start < g.rules.length
  · have hstart : (newGrammar toChar g).start = ⟨g.start, lt_ntCount_of_lt g hs⟩ := by
      simp [newGrammar, newStart, hs]
    have htr : toTotal toChar g (.nt g.start) = .nonterminal ⟨g.start, lt_ntCount_of_lt g hs⟩ := by
      simp [toTotal, ntE, hs, lt_ntCount_of_lt g hs]
    rw [hstart]
    constructor
    · intro hrec
      obtain ⟨o, D⟩ := htot g.start (v.map toChar)
      obtain ⟨⟨r, E, R⟩, -⟩ := sim hinj D (Or.inr ⟨_, rfl⟩) v rfl
      rw [htr] at E
      have := External.LoffForwardRepaired.PegGrammar.evaluates_deterministic E hrec
      subst this
      cases o with
      | fail => cases R
      | ok t rest =>
          obtain ⟨u, hu, hr⟩ := R
          cases hr
          subst hu
          exact ⟨t, by simpa using D⟩
    · rintro ⟨t, D⟩
      obtain ⟨⟨r, E, R⟩, -⟩ := sim hinj D (Or.inr ⟨_, rfl⟩) v rfl
      rw [htr] at E
      obtain ⟨u, hu, rfl⟩ := R
      obtain rfl : u = [] := List.map_eq_nil_iff.mp hu.symm
      exact E
  · have hstart : (newGrammar toChar g).rule (newGrammar toChar g).start = .failure := by
      have h1 : ¬ 2 * g.rules.length + (allSubs g).length < g.rules.length := by omega
      have h2 : ¬ 2 * g.rules.length + (allSubs g).length < 2 * g.rules.length := by omega
      simp [newGrammar, newStart, hs, newRule, h1, h2]
    constructor
    · intro hrec
      cases hrec with
      | nonterminal h =>
          rw [hstart] at h
          cases h
    · rintro ⟨t, D⟩
      cases D with
      | ntOk _ e _ _ _ hr _ => exact absurd (ruleAt_eq_some hr).1 hs

end PegSeparation.Closure.PartialPEG
