import PegSeparation.Closure.PartialPEGTranslate

/-!
# Basic facts about the translation of `PartialPEG` grammars

Evaluation of the building blocks (`choiceOf`, `litE`, `ntE`), the shape of the rules of the
translated grammar, the suffix property of both semantics, and the fact that `trP e` only ever
succeeds by consuming input (`trP_strict`), on every input.
-/

set_option linter.unusedSectionVars false

namespace PegSeparation.Closure.PartialPEG

open PegSeparation PegSeparation.PegGrammar

theorem beqChar_iff {c d : Char} : beqChar c d = true ↔ c = d := by
  simp [beqChar, Char.toNat_inj]

theorem stripPrefix?_eq_some {s x rest : List Char} (h : stripPrefix? s x = some rest) :
    x = s ++ rest := by
  induction s generalizing x with
  | nil => simp only [stripPrefix?, Option.some.injEq] at h; simp [h]
  | cons c cs ih =>
      cases x with
      | nil => simp [stripPrefix?] at h
      | cons d ds =>
          simp only [stripPrefix?] at h
          split at h
          · rename_i hcd
            rw [beqChar_iff] at hcd
            subst hcd
            simp [ih h]
          · simp at h

/-- The rest of a successful derivation is a suffix of the input. -/
theorem derives_rest_suffix {g : Grammar} {e : PExp} {x : List Char} {o : Outcome}
    (D : Derives g e x o) : ∀ {t rest}, o = .ok t rest → rest <:+ x := by
  induction D with
  | eps => intro t rest h; cases h; exact List.suffix_refl _
  | anyOk c r => intro t rest h; cases h; exact List.suffix_cons _ _
  | chrOk c d r _ => intro t rest h; cases h; exact List.suffix_cons _ _
  | rangeOk lo hi d r _ => intro t rest h; cases h; exact List.suffix_cons _ _
  | litOk s inp r hs =>
      intro t rest h; cases h; rw [stripPrefix?_eq_some hs]; exact List.suffix_append _ _
  | ntOk i e inp r t _ _ ih => intro t' rest h; cases h; exact ih rfl
  | seqOk e₁ e₂ inp r₁ r₂ t₁ t₂ _ _ ih₁ ih₂ =>
      intro t rest h; cases h; exact (ih₂ rfl).trans (ih₁ rfl)
  | altL e₁ e₂ inp r t _ ih => intro t' rest h; cases h; exact ih rfl
  | altR e₁ e₂ inp r t _ _ _ ih => intro t' rest h; cases h; exact ih rfl
  | starNil e inp _ _ => intro t rest h; cases h; exact List.suffix_refl _
  | starCons e inp r r' t ts _ _ ih₁ ih₂ =>
      intro t' rest h; cases h; exact (ih₂ rfl).trans (ih₁ rfl)
  | notFail e inp _ _ => intro t rest h; cases h; exact List.suffix_refl _
  | _ => intro t rest h; cases h

theorem eq_of_suffix_squeeze {α : Type} {a b c : List α} (h₁ : a <:+ b) (h₂ : b <:+ c)
    (h : a = c) : b = c := by
  subst h
  exact h₂.eq_of_length (le_antisymm h₂.length_le h₁.length_le)

section Basic

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
  {toChar : Terminal → Char} {n : Nat} {G : PegGrammar Terminal n}

theorem pre_eq_some (hinj : Function.Injective toChar) {c : Char} {t : Terminal} :
    pre toChar c = some t ↔ toChar t = c := by
  unfold pre
  split
  · rename_i h
    constructor
    · intro e; cases e; exact h.choose_spec
    · intro e; exact congrArg some (hinj (h.choose_spec.trans e.symm))
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    exact fun e => h ⟨t, e⟩

theorem pre_eq_none {c : Char} (h : pre toChar c = none) (t : Terminal) : toChar t ≠ c := by
  unfold pre at h
  split at h
  · simp at h
  · rename_i h'; exact fun e => h' ⟨t, e⟩

theorem eval_terminal_cons (t t' : Terminal) (u : List Terminal) :
    G.Evaluates (.terminal t) (t' :: u) (if t' = t then .success u else .failure) := by
  have := Evaluates.terminal (grammar := G) t (t' :: u)
  by_cases h : t' = t <;> simpa [terminalResult, h] using this

theorem eval_terminal_nil (t : Terminal) : G.Evaluates (.terminal t) [] .failure :=
  Evaluates.terminal (grammar := G) t []

theorem eval_choiceOf_nil (l : List Terminal) : G.Evaluates (choiceOf l) [] .failure := by
  induction l with
  | nil => exact .failure _
  | cons t ts ih => exact .choiceRight (eval_terminal_nil t) ih

theorem eval_choiceOf_cons (l : List Terminal) (t : Terminal) (u : List Terminal) :
    G.Evaluates (choiceOf l) (t :: u) (if t ∈ l then .success u else .failure) := by
  induction l with
  | nil => simpa [choiceOf] using Evaluates.failure (grammar := G) (t :: u)
  | cons t' ts ih =>
      have ht := eval_terminal_cons (G := G) t' t u
      by_cases h : t = t'
      · subst h; simp only [if_true] at ht; simpa [choiceOf] using Evaluates.choiceLeft ht
      · simp only [h, if_false] at ht
        have := Evaluates.choiceRight (right := choiceOf ts) ht ih
        by_cases hm : t ∈ ts <;> simpa [choiceOf, h, hm] using this

theorem eval_litE_ok (hinj : Function.Injective toChar) :
    ∀ (s : List Char) (v : List Terminal) (rest : List Char),
      stripPrefix? s (v.map toChar) = some rest →
      ∃ u, rest = u.map toChar ∧ G.Evaluates (litE toChar s) v (.success u)
  | [], v, rest, h => by
      simp only [stripPrefix?, Option.some.injEq] at h
      exact ⟨v, h.symm, .empty v⟩
  | c :: cs, [], rest, h => by simp [stripPrefix?] at h
  | c :: cs, t :: v, rest, h => by
      simp only [List.map_cons, stripPrefix?] at h
      split at h
      · rename_i hc
        rw [beqChar_iff] at hc
        obtain ⟨u, hu, hev⟩ := eval_litE_ok hinj cs v rest h
        refine ⟨u, hu, ?_⟩
        have hp : pre toChar c = some t := (pre_eq_some hinj).mpr hc.symm
        simp only [litE, hp]
        have ht := eval_terminal_cons (G := G) t t v
        simp only [if_true] at ht
        exact .sequenceSuccess ht hev
      · simp at h

theorem eval_litE_fail (hinj : Function.Injective toChar) :
    ∀ (s : List Char) (v : List Terminal),
      stripPrefix? s (v.map toChar) = none → G.Evaluates (litE toChar s) v .failure
  | [], v, h => by simp [stripPrefix?] at h
  | c :: cs, v, h => by
      simp only [litE]
      cases hp : pre toChar c with
      | none => exact .failure _
      | some t =>
          have htc := (pre_eq_some hinj).mp hp
          cases v with
          | nil => exact .sequenceFailure (eval_terminal_nil t)
          | cons t' v =>
              simp only [List.map_cons, stripPrefix?] at h
              have ht := eval_terminal_cons (G := G) t t' v
              split at h
              · rename_i hc
                rw [beqChar_iff] at hc
                have : t' = t := hinj (by rw [htc, hc])
                subst this
                simp only [if_true] at ht
                exact .sequenceSuccess ht (eval_litE_fail hinj cs v h)
              · rename_i hc
                have hne : t' ≠ t := by
                  rintro rfl; exact hc (by rw [beqChar_iff, htc])
                simp only [hne, if_false] at ht
                exact .sequenceFailure ht

/-- Total evaluation of nonterminal-free building blocks. -/
theorem choiceOf_total (l : List Terminal) (v : List Terminal) :
    ∃ r, G.Evaluates (choiceOf l) v r := by
  cases v with
  | nil => exact ⟨_, eval_choiceOf_nil l⟩
  | cons t u => exact ⟨_, eval_choiceOf_cons l t u⟩

theorem litE_total (s : List Char) (v : List Terminal) :
    ∃ r, G.Evaluates (litE toChar s) v r := by
  induction s generalizing v with
  | nil => exact ⟨_, .empty v⟩
  | cons c cs ih =>
      simp only [litE]
      cases pre toChar c with
      | none => exact ⟨_, .failure v⟩
      | some t =>
          exact PartialTotalityHelpers.sequence_total ⟨_, Evaluates.terminal t v⟩ ih

/-- The remaining input of a success is a suffix. -/
theorem eval_suffix {e : ParsingExpression Terminal n} {v : List Terminal}
    {r : ParseResult Terminal} (h : G.Evaluates e v r) : ∀ {u}, r = .success u → u <:+ v := by
  induction h with
  | empty => intro u h; cases h; exact List.suffix_refl _
  | failure => intro u h; cases h
  | terminal t input =>
      intro u h
      cases input with
      | nil => simp [terminalResult] at h
      | cons a rest =>
          simp only [terminalResult] at h
          split at h
          · cases h; exact List.suffix_cons _ _
          · cases h
  | nonterminal _ ih => exact ih
  | sequenceFailure _ _ => intro u h; cases h
  | sequenceSuccess _ _ ih₁ ih₂ => intro u h; exact (ih₂ h).trans (ih₁ rfl)
  | choiceLeft _ ih => exact ih
  | choiceRight _ _ _ ih => exact ih
  | notSuccess _ _ => intro u h; cases h; exact List.suffix_refl _
  | notFailure _ _ => intro u h; cases h
  | andSuccess _ _ => intro u h; cases h; exact List.suffix_refl _
  | andFailure _ _ => intro u h; cases h

end Basic

section Rules

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
  (toChar : Terminal → Char) (g : Grammar)

theorem ntE_eval {j : Nat} (hj : j < ntCount g) {v : List Terminal} {r : ParseResult Terminal}
    (h : (newGrammar toChar g).Evaluates (newRule toChar g ⟨j, hj⟩) v r) :
    (newGrammar toChar g).Evaluates (ntE g j) v r := by
  simp only [ntE, hj, dif_pos]
  exact .nonterminal h

theorem ntE_eval_inv {j : Nat} (hj : j < ntCount g) {v : List Terminal}
    {r : ParseResult Terminal} (h : (newGrammar toChar g).Evaluates (ntE g j) v r) :
    (newGrammar toChar g).Evaluates (newRule toChar g ⟨j, hj⟩) v r := by
  simp only [ntE, hj, dif_pos] at h
  cases h with
  | nonterminal h => exact h

theorem lt_ntCount_of_lt {i : Nat} (hi : i < g.rules.length) : i < ntCount g := by
  unfold ntCount; omega

theorem add_lt_ntCount_of_lt {i : Nat} (hi : i < g.rules.length) :
    g.rules.length + i < ntCount g := by
  unfold ntCount; omega

theorem newRule_lt {i : Nat} (hi : i < g.rules.length) :
    newRule toChar g ⟨i, lt_ntCount_of_lt g hi⟩ = toTotal toChar g g.rules[i] := by
  simp [newRule, hi]

theorem newRule_add {i : Nat} (hi : i < g.rules.length) :
    newRule toChar g ⟨g.rules.length + i, add_lt_ntCount_of_lt g hi⟩ = trP toChar g g.rules[i] := by
  have h1 : ¬ g.rules.length + i < g.rules.length := by omega
  have h2 : g.rules.length + i < 2 * g.rules.length := by omega
  simp only [newRule, h1, h2, dif_neg, dif_pos, not_false_eq_true]
  congr 2
  omega

theorem starIdx_lt (a : PExp) : starIdx g a < ntCount g := by
  have := List.idxOf_le_length (a := PExp.star a) (l := allSubs g)
  unfold starIdx ntCount; omega

theorem newRule_starIdx {a : PExp} (ha : PExp.star a ∈ allSubs g) :
    newRule toChar g ⟨starIdx g a, starIdx_lt g a⟩ =
      .orderedChoice (.sequence (trP toChar g a) (ntE g (starIdx g a))) .empty := by
  have hk := List.idxOf_lt_length_of_mem ha
  have h1 : ¬ starIdx g a < g.rules.length := by unfold starIdx; omega
  have h2 : ¬ starIdx g a < 2 * g.rules.length := by unfold starIdx; omega
  have h3 : starIdx g a - 2 * g.rules.length < (allSubs g).length := by unfold starIdx; omega
  simp only [newRule, h1, h2, h3, dif_neg, dif_pos, not_false_eq_true]
  have hidx : starIdx g a - 2 * g.rules.length = (allSubs g).idxOf (.star a) := by
    unfold starIdx; omega
  simp only [hidx, List.getElem_idxOf]
  rfl

theorem newRule_star_not_mem {a : PExp} (ha : PExp.star a ∉ allSubs g) :
    newRule toChar g ⟨starIdx g a, starIdx_lt g a⟩ = .failure := by
  have hk := List.idxOf_eq_length ha
  have h1 : ¬ starIdx g a < g.rules.length := by unfold starIdx; omega
  have h2 : ¬ starIdx g a < 2 * g.rules.length := by unfold starIdx; omega
  have h3 : ¬ starIdx g a - 2 * g.rules.length < (allSubs g).length := by unfold starIdx; omega
  simp [newRule, h1, h2, h3]

end Rules

section Strict

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
  (toChar : Terminal → Char) (g : Grammar)

/-- Expressions that can only succeed by consuming input (given that the nonterminals
`L + i` do). -/
inductive Consuming : ParsingExpression Terminal (ntCount g) → Prop
  | failure : Consuming .failure
  | terminal (t : Terminal) : Consuming (.terminal t)
  | choice {a b} : Consuming a → Consuming b → Consuming (.orderedChoice a b)
  | seqL {a b} : Consuming a → Consuming (.sequence a b)
  | seqR {a b} : Consuming b → Consuming (.sequence a b)
  | ntP (j : Fin (ntCount g)) : g.rules.length ≤ j.val → j.val < 2 * g.rules.length →
      Consuming (.nonterminal j)

theorem consuming_choiceOf (l : List Terminal) : Consuming g (choiceOf l) := by
  induction l with
  | nil => exact .failure
  | cons t ts ih => exact .choice (.terminal t) ih

theorem consuming_litE {s : List Char} (hs : s ≠ []) : Consuming g (litE toChar s) := by
  cases s with
  | nil => exact absurd rfl hs
  | cons c cs =>
      simp only [litE]
      cases pre toChar c with
      | none => exact .failure
      | some t => exact .seqL (.terminal t)

theorem consuming_trP (e : PExp) : Consuming g (trP toChar g e) := by
  induction e with
  | eps => exact .failure
  | any => exact consuming_choiceOf g _
  | chr c =>
      simp only [trP]
      cases pre toChar c with
      | none => exact .failure
      | some t => exact .terminal t
  | range lo hi => exact consuming_choiceOf g _
  | lit s =>
      simp only [trP]
      split
      · exact .failure
      · rename_i hs; exact consuming_litE toChar g hs
  | nt i =>
      simp only [trP]
      split
      · rename_i hi
        have := add_lt_ntCount_of_lt g hi
        simp only [ntE, this, dif_pos]
        exact .ntP _ (by simp) (by simp; omega)
      · exact .failure
  | seq a b iha ihb => exact .choice (.seqL iha) (.seqR ihb)
  | alt a b iha ihb => exact .choice iha (.seqR ihb)
  | star a iha => exact .seqL iha
  | notP a _ => exact .failure

theorem consuming_strict {e : ParsingExpression Terminal (ntCount g)} {v : List Terminal}
    {r : ParseResult Terminal} (h : (newGrammar toChar g).Evaluates e v r) :
    Consuming g e → ∀ {u}, r = .success u → u ≠ v := by
  induction h with
  | empty => intro hc; cases hc
  | failure => intro _ u h; cases h
  | terminal t input =>
      intro _ u h
      cases input with
      | nil => simp [terminalResult] at h
      | cons a rest =>
          simp only [terminalResult] at h
          split at h
          · cases h; intro e; exact absurd (congrArg List.length e) (by simp)
          · cases h
  | @nonterminal name _ _ body ih =>
      intro hc
      cases hc with
      | ntP _ h1 h2 =>
          apply ih
          have hi : name.val - g.rules.length < g.rules.length := by omega
          have hr := newRule_add toChar g hi
          have hname : (⟨g.rules.length + (name.val - g.rules.length),
              add_lt_ntCount_of_lt g hi⟩ : Fin (ntCount g)) = name := by
            ext; simp; omega
          rw [hname] at hr
          change Consuming g (newRule toChar g name)
          rw [hr]
          exact consuming_trP toChar g _
  | sequenceFailure _ _ => intro _ u h; cases h
  | sequenceSuccess h₁ h₂ ih₁ ih₂ =>
      intro hc u hu
      have s₂ := eval_suffix h₂ hu
      have s₁ := eval_suffix h₁ rfl
      cases hc with
      | seqL hc =>
          intro e
          exact ih₁ hc rfl (eq_of_suffix_squeeze s₂ s₁ e)
      | seqR hc =>
          intro e; subst e
          exact ih₂ hc hu (s₁.eq_of_length (le_antisymm s₁.length_le s₂.length_le)).symm
  | choiceLeft _ ih => intro hc; cases hc with | choice ha _ => exact ih ha
  | choiceRight _ _ _ ih => intro hc; cases hc with | choice _ hb => exact ih hb
  | notSuccess _ _ => intro hc; cases hc
  | notFailure _ _ => intro _ u h; cases h
  | andSuccess _ _ => intro hc; cases hc
  | andFailure _ _ => intro _ u h; cases h

/-- `trP e` succeeds only by consuming input, on every input. -/
theorem trP_strict {e : PExp} {v u : List Terminal}
    (h : (newGrammar toChar g).Evaluates (trP toChar g e) v (.success u)) : u ≠ v :=
  consuming_strict toChar g h (consuming_trP toChar g e) rfl

end Strict

end PegSeparation.Closure.PartialPEG
