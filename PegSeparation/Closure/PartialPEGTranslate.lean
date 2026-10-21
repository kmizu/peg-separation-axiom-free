import PegSeparation.Closure.PartialPEGDeterminism
import PegSeparation.Common.Recognition
import PegSeparation.External.PartialTotalization.TotalityHelpers

/-!
# Translating `lean4-peg` PEGs into the artifact's PEGs

`PartialPEG` grammars (copied from `lean4-peg`) are over `Char`, have repetition `e*`, character
classes, literals and the wildcard, and a partial semantics. Here we translate such a grammar `g`
into a `PegGrammar Terminal (ntCount g)` over a finite alphabet `Terminal` embedded in `Char` by
`toChar`.

Nonterminals of the translated grammar (`L = g.rules.length`, `K = (allSubs g).length`):

- `i < L`: the translation `toTotal e` of rule `i` of `g` (`e = g.rules[i]`);
- `L + i`: the *consuming* translation `trP e` of rule `i`, which succeeds exactly when `e` succeeds
  and consumes at least one character (with the same rest);
- `2L + k`: for the `k`-th subterm of the rules of `g`, when it is a repetition `a*`, the rule
  `X ← trP(a) X / ε` (repetition stopped by a nonconsuming iteration instead of looping);
- `2L + K`: a failing nonterminal, used as start symbol when `g.start` has no rule.

Using `trP` in the repetition rule makes every repetition nonterminal terminate on every input,
while on the inputs where `g`'s repetition terminates the two agree (there a nonconsuming
iteration never happens).
-/

set_option linter.unusedSectionVars false

namespace PegSeparation.Closure.PartialPEG

open PegSeparation

deriving instance DecidableEq for PExp

/-- All subterms of an expression (itself included). -/
def subterms : PExp → List PExp
  | .eps => [.eps]
  | .any => [.any]
  | .chr c => [.chr c]
  | .range lo hi => [.range lo hi]
  | .lit s => [.lit s]
  | .nt i => [.nt i]
  | .seq a b => .seq a b :: (subterms a ++ subterms b)
  | .alt a b => .alt a b :: (subterms a ++ subterms b)
  | .star a => .star a :: subterms a
  | .notP a => .notP a :: subterms a

theorem mem_subterms_self (e : PExp) : e ∈ subterms e := by
  cases e <;> simp [subterms]

theorem subterms_trans {e x y : PExp} (hx : x ∈ subterms e) (hy : y ∈ subterms x) :
    y ∈ subterms e := by
  induction e with
  | eps | any | chr _ | range _ _ | lit _ | nt _ =>
      simp only [subterms, List.mem_singleton] at hx; subst hx; exact hy
  | seq a b iha ihb =>
      simp only [subterms, List.mem_cons, List.mem_append] at hx ⊢
      rcases hx with rfl | hx | hx
      · simpa [subterms] using hy
      · exact Or.inr (Or.inl (iha hx))
      · exact Or.inr (Or.inr (ihb hx))
  | alt a b iha ihb =>
      simp only [subterms, List.mem_cons, List.mem_append] at hx ⊢
      rcases hx with rfl | hx | hx
      · simpa [subterms] using hy
      · exact Or.inr (Or.inl (iha hx))
      · exact Or.inr (Or.inr (ihb hx))
  | star a iha =>
      simp only [subterms, List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · simpa [subterms] using hy
      · exact Or.inr (iha hx)
  | notP a iha =>
      simp only [subterms, List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · simpa [subterms] using hy
      · exact Or.inr (iha hx)

/-- The subterms of all rules of `g`. -/
def allSubs (g : Grammar) : List PExp := g.rules.flatMap subterms

/-- Number of nonterminals of the translated grammar. -/
def ntCount (g : Grammar) : Nat := 2 * g.rules.length + (allSubs g).length + 1

theorem mem_allSubs_of_sub {g : Grammar} {x y : PExp} (hx : x ∈ allSubs g)
    (hy : y ∈ subterms x) : y ∈ allSubs g := by
  obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.mp hx
  exact List.mem_flatMap.mpr ⟨r, hr, subterms_trans hxr hy⟩

theorem rule_mem_allSubs {g : Grammar} {i : Nat} (hi : i < g.rules.length) :
    g.rules[i] ∈ allSubs g :=
  List.mem_flatMap.mpr ⟨g.rules[i], List.getElem_mem hi, mem_subterms_self _⟩

theorem ruleAt_eq_getElem? (rs : List PExp) (i : Nat) : ruleAt rs i = rs[i]? := by
  induction rs generalizing i with
  | nil => rfl
  | cons r rs ih => cases i <;> simp [ruleAt, ih]

theorem ruleAt_eq_some {rs : List PExp} {i : Nat} {e : PExp} (h : ruleAt rs i = some e) :
    ∃ hi : i < rs.length, rs[i] = e := by
  rw [ruleAt_eq_getElem?] at h
  exact List.getElem?_eq_some_iff.mp h

theorem ruleAt_eq_none {rs : List PExp} {i : Nat} (h : ruleAt rs i = none) : ¬ i < rs.length := by
  rw [ruleAt_eq_getElem?, List.getElem?_eq_none_iff] at h
  omega

section Translation

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
  (toChar : Terminal → Char) (g : Grammar)

/-- The terminal whose character is `c`, if any. -/
noncomputable def pre (c : Char) : Option Terminal :=
  if h : ∃ t, toChar t = c then some h.choose else none

/-- All terminals. -/
noncomputable def univList : List Terminal := (Finset.univ : Finset Terminal).toList

/-- Ordered choice of single terminals. -/
def choiceOf {n : Nat} : List Terminal → ParsingExpression Terminal n
  | [] => .failure
  | t :: ts => .orderedChoice (.terminal t) (choiceOf ts)

/-- A literal string (failure if some character is not the image of a terminal). -/
noncomputable def litE {n : Nat} : List Char → ParsingExpression Terminal n
  | [] => .empty
  | c :: cs =>
      match pre toChar c with
      | some t => .sequence (.terminal t) (litE cs)
      | none => .failure

/-- A nonterminal by index (failure when out of range). -/
def ntE (j : Nat) : ParsingExpression Terminal (ntCount g) :=
  if h : j < ntCount g then .nonterminal ⟨j, h⟩ else .failure

/-- The repetition nonterminal for `a*`. -/
def starIdx (a : PExp) : Nat := 2 * g.rules.length + (allSubs g).idxOf (.star a)

/-- The terminals in a character class. -/
noncomputable def rangeList (lo hi : Char) : List Terminal :=
  (univList (Terminal := Terminal)).filter fun t => leChar lo (toChar t) && leChar (toChar t) hi

/-- The translation of an expression. -/
noncomputable def toTotal : PExp → ParsingExpression Terminal (ntCount g)
  | .eps => .empty
  | .any => choiceOf univList
  | .chr c =>
      match pre toChar c with
      | some t => .terminal t
      | none => .failure
  | .range lo hi => choiceOf (rangeList toChar lo hi)
  | .lit s => litE toChar s
  | .nt i => if i < g.rules.length then ntE g i else .failure
  | .seq a b => .sequence (toTotal a) (toTotal b)
  | .alt a b => .orderedChoice (toTotal a) (toTotal b)
  | .star a => ntE g (starIdx g a)
  | .notP a => .notPredicate (toTotal a)

/-- The consuming translation: succeeds iff the expression succeeds consuming input. -/
noncomputable def trP : PExp → ParsingExpression Terminal (ntCount g)
  | .eps => .failure
  | .any => choiceOf univList
  | .chr c =>
      match pre toChar c with
      | some t => .terminal t
      | none => .failure
  | .range lo hi => choiceOf (rangeList toChar lo hi)
  | .lit s => if s = [] then .failure else litE toChar s
  | .nt i => if i < g.rules.length then ntE g (g.rules.length + i) else .failure
  | .seq a b =>
      .orderedChoice (.sequence (trP a) (toTotal toChar g b))
        (.sequence (.sequence (.notPredicate (trP a)) (.andPredicate (toTotal toChar g a))) (trP b))
  | .alt a b => .orderedChoice (trP a) (.sequence (.notPredicate (toTotal toChar g a)) (trP b))
  | .star a => .sequence (trP a) (ntE g (starIdx g a))
  | .notP _ => .failure

/-- The rule of the repetition nonterminal `j` of a subterm. -/
noncomputable def starRule (j : Nat) : PExp → ParsingExpression Terminal (ntCount g)
  | .star a => .orderedChoice (.sequence (trP toChar g a) (ntE g j)) .empty
  | _ => .failure

/-- The rules of the translated grammar. -/
noncomputable def newRule (j : Fin (ntCount g)) : ParsingExpression Terminal (ntCount g) :=
  if h1 : j.val < g.rules.length then toTotal toChar g g.rules[j.val]
  else if h2 : j.val < 2 * g.rules.length then
    trP toChar g (g.rules[j.val - g.rules.length]'(by omega))
  else if h3 : j.val - 2 * g.rules.length < (allSubs g).length then
    starRule toChar g j.val (allSubs g)[j.val - 2 * g.rules.length]
  else .failure

/-- The start symbol of the translated grammar. -/
def newStart : Fin (ntCount g) :=
  if h : g.start < g.rules.length then ⟨g.start, by unfold ntCount; omega⟩
  else ⟨2 * g.rules.length + (allSubs g).length, by unfold ntCount; omega⟩

/-- The translated grammar. -/
noncomputable def newGrammar : PegGrammar Terminal (ntCount g) where
  rule := newRule toChar g
  start := newStart g

end Translation

end PegSeparation.Closure.PartialPEG
