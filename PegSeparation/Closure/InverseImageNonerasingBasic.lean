import PegSeparation.Closure.InverseImageNonerasingDefs

set_option linter.unusedSectionVars false

/-!
# Inverse images under nonerasing homomorphisms: basic facts

Evaluation of the helper expressions (`chain`, `guardEq`), membership in the state and item
lists, the rule of an item's code, and how the image is read letter by letter.
-/

namespace PegSeparation.Closure.InverseImageNonerasing

open PegSeparation PegSeparation.PegGrammar

section Generic

variable {Source : Type} [DecidableEq Source] {n : ℕ} {G : PegGrammar Source n}

/-- A chain fails when every member fails. -/
theorem chain_fail {α : Type} {l : List α} {F : α → ParsingExpression Source n}
    {u : List Source} (h : ∀ y ∈ l, G.Evaluates (F y) u .failure) :
    G.Evaluates (chain l F) u .failure := by
  induction l with
  | nil => exact .failure u
  | cons y l ih =>
      exact .choiceRight (h y (by simp)) (ih (fun y' hy' => h y' (by simp [hy'])))

/-- A chain whose only non-failing member is `y₁` evaluates like that member. -/
theorem chain_pick {α : Type} {l : List α} {F : α → ParsingExpression Source n}
    {u : List Source} {y₁ : α} {R : ParseResult Source} (hy₁ : y₁ ∈ l)
    (hR : G.Evaluates (F y₁) u R) (hother : ∀ y ∈ l, y ≠ y₁ → G.Evaluates (F y) u .failure) :
    G.Evaluates (chain l F) u R := by
  induction l with
  | nil => simp at hy₁
  | cons y l ih =>
      by_cases hy : y = y₁
      · subst hy
        cases R with
        | success rest => exact .choiceLeft hR
        | failure =>
            refine .choiceRight hR (chain_fail (fun y' hy' => ?_))
            by_cases h' : y' = y
            · subst h'; exact hR
            · exact hother y' (by simp [hy']) h'
      · have hy₁' : y₁ ∈ l := by
          rcases List.mem_cons.mp hy₁ with h | h
          · exact absurd h.symm hy
          · exact h
        exact .choiceRight (hother y (by simp) hy)
          (ih hy₁' (fun y' hy' hne => hother y' (by simp [hy']) hne))

/-- A guard evaluates to the outcome of ending at its first state without consuming. -/
theorem guardEq_eval (q q' : St Source) (u : List Source) :
    G.Evaluates (guardEq q q') u (outcome q u q') := by
  unfold guardEq outcome
  split_ifs
  · exact .empty u
  · exact .failure u

/-- An `if` between `ε` and failure. -/
theorem ite_eval (p : Prop) [Decidable p] (u : List Source) :
    G.Evaluates (if p then .empty else .failure) u (if p then .success u else .failure) := by
  split_ifs
  · exact .empty u
  · exact .failure u

/-- A chain over a family hitting `q₁` succeeds with the hit's rest. -/
theorem chain_hits {l : List (St Source)} {F : St Source → ParsingExpression Source n}
    {u u₁ : List Source} {q₁ : St Source} (hq₁ : q₁ ∈ l)
    (h : ∀ q' ∈ l, G.Evaluates (F q') u (outcome q₁ u₁ q')) :
    G.Evaluates (chain l F) u (.success u₁) := by
  refine chain_pick hq₁ ?_ (fun y hy hne => ?_)
  · simpa [outcome] using h q₁ hq₁
  · simpa [outcome, hne] using h y hy

end Generic

section Subs

variable {T : Type} {n : ℕ}

/-- Every expression is among its subexpressions. -/
theorem self_mem_subs (e : ParsingExpression T n) : e ∈ subs e := by
  cases e <;> simp [subs]

/-- The subexpressions are closed under taking subexpressions. -/
theorem subs_trans {e x y : ParsingExpression T n} (hx : x ∈ subs e) (hy : y ∈ subs x) :
    y ∈ subs e := by
  induction e with
  | sequence a b iha ihb =>
      simp only [subs, List.mem_cons, List.mem_append] at hx ⊢
      rcases hx with rfl | hx | hx
      · simpa [subs] using hy
      · exact Or.inr (Or.inl (iha hx))
      · exact Or.inr (Or.inr (ihb hx))
  | orderedChoice a b iha ihb =>
      simp only [subs, List.mem_cons, List.mem_append] at hx ⊢
      rcases hx with rfl | hx | hx
      · simpa [subs] using hy
      · exact Or.inr (Or.inl (iha hx))
      · exact Or.inr (Or.inr (ihb hx))
  | notPredicate a iha =>
      simp only [subs, List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · simpa [subs] using hy
      · exact Or.inr (iha hx)
  | andPredicate a iha =>
      simp only [subs, List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · simpa [subs] using hy
      · exact Or.inr (iha hx)
  | empty | failure | terminal _ | nonterminal _ =>
      simp only [subs, List.mem_singleton] at hx
      subst hx; simpa [subs] using hy

end Subs

section Defs

variable {Source Target : Type} [Fintype Source] [DecidableEq Source] [DecidableEq Target]
  {m : ℕ}

variable (hom : WordHom Source Target) (g : PegGrammar Target m)

/-- Every letter is listed. -/
theorem mem_letters (a : Source) : a ∈ letters (Source := Source) := by
  simp [letters]

/-- The boundary state is listed. -/
theorem none_mem_stList : (none : St Source) ∈ stList hom := by
  simp [stList]

/-- The inner states are exactly the offsets strictly inside a block. -/
theorem some_mem_stList_iff {a : Source} {i : ℕ} :
    some (a, i) ∈ stList hom ↔ 1 ≤ i ∧ i < (hom.letterImage a).length := by
  simp only [stList, List.mem_cons, reduceCtorEq, false_or, List.mem_flatMap, List.mem_map,
    List.mem_range, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨b, _, j, hj, rfl, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨a, mem_letters a, i - 1, by omega, rfl, by omega⟩

/-- The next state is listed. -/
theorem nextSt_mem {a : Source} {i : ℕ} : nextSt hom a i ∈ stList hom := by
  unfold nextSt
  split_ifs with h
  · exact (some_mem_stList_iff hom).mpr ⟨by omega, h⟩
  · exact none_mem_stList hom

/-- The image after the letter at offset `i` of the block of `a`. -/
theorem img_nextSt {a : Source} {i : ℕ} (hi : i < (hom.letterImage a).length)
    (u : List Source) :
    img hom (nextSt hom a i) u = (hom.letterImage a).drop (i + 1) ++ hom.extend u := by
  unfold nextSt
  split_ifs with h
  · rfl
  · have : (hom.letterImage a).drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
    simp [img, this]

/-- Dropping up to a valid offset exposes the letter there. -/
theorem drop_eq_getElem_cons {l : List Target} {i : ℕ} (hi : i < l.length) :
    l.drop i = l[i] :: l.drop (i + 1) :=
  List.drop_eq_getElem_cons hi

/-- A rule body of `g` is in the closure. -/
theorem rule_mem_closure (i : Fin m) : g.rule i ∈ closure g := by
  simp only [closure, List.mem_flatMap]
  exact ⟨i, List.mem_finRange i, self_mem_subs _⟩

/-- The closure is closed under immediate subexpressions. -/
theorem closure_sub {e x : ParsingExpression Target m} (he : e ∈ closure g)
    (hx : x ∈ subs e) : x ∈ closure g := by
  simp only [closure, List.mem_flatMap] at he ⊢
  obtain ⟨i, hi, he⟩ := he
  exact ⟨i, hi, subs_trans he hx⟩

/-- Membership in the item list. -/
theorem mem_items {e : ParsingExpression Target m} {q q' : St Source} :
    (e, q, q') ∈ items hom g ↔ e ∈ closure g ∧ q ∈ stList hom ∧ q' ∈ stList hom := by
  simp only [items, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨e', he', q₀, hq₀, q₁, hq₁, rfl, rfl, rfl⟩
    exact ⟨he', hq₀, hq₁⟩
  · rintro ⟨he, hq, hq'⟩
    exact ⟨e, he, q, hq, q', hq', rfl, rfl, rfl⟩

/-- The rule at the code of an item is its body. -/
theorem rule_code {x : Item Source Target m} (hx : x ∈ items hom g) :
    (grammar hom g).rule (code hom g x) = body hom g x := by
  classical
  have hlt := List.idxOf_lt_length_iff.mpr hx
  simp only [grammar, code, dif_pos hx]
  rw [dif_pos hlt]
  congr 1
  exact List.getElem_idxOf hlt

/-- A call of an item evaluates like its body. -/
theorem N_eval {x : Item Source Target m} (hx : x ∈ items hom g) {u : List Source}
    {R : ParseResult Source} (h : (grammar hom g).Evaluates (body hom g x) u R) :
    (grammar hom g).Evaluates (N hom g x) u R := by
  refine .nonterminal ?_
  rw [rule_code hom g hx]
  exact h

end Defs

end PegSeparation.Closure.InverseImageNonerasing
