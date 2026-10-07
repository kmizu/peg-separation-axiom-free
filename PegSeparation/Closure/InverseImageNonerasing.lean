import PegSeparation.Closure.InverseImageNonerasingComplete

/-!
# Inverse images of total-PEG languages under nonerasing homomorphisms

`recognizedByTotalPEG_inverseImage_nonerasing`: if a total PEG recognizes `L`, a total PEG
recognizes `hom⁻¹(L)` for every nonerasing `hom`, proved without the external
Birman–Ullman axiom.

The simulating grammar (`InverseImageNonerasingDefs`) is complete (`complete`). Since the
original grammar is total, completeness already shows that every rule of the simulating
grammar evaluates on every input (`nonterminal_total`), hence the simulating grammar is total;
and, by determinism of evaluation, that it accepts exactly the words whose image `g` accepts
(`recognizes_iff`).
-/

set_option linter.unusedSectionVars false

namespace PegSeparation.Closure.InverseImageNonerasing

open PegSeparation PegSeparation.PegGrammar

section Defs

variable {Source Target : Type} [Fintype Source] [DecidableEq Source] [DecidableEq Target]
  {m : ℕ}

variable (hom : WordHom Source Target) (g : PegGrammar Target m)

/-- The call of every item evaluates on every source word. -/
theorem N_total (hne : ∀ a, hom.letterImage a ≠ []) (total : g.IsLoffTotal)
    {x : Item Source Target m} (hx : x ∈ items hom g) (u : List Source) :
    ∃ R, (grammar hom g).Evaluates (N hom g x) u R := by
  obtain ⟨e, q, q'⟩ := x
  obtain ⟨he, hq, hq'⟩ := (mem_items hom g).mp hx
  obtain ⟨r, D⟩ := total e (img hom q u)
  have hsim := complete hom g hne D q u hq rfl he
  cases r with
  | failure => exact ⟨_, hsim q' hq'⟩
  | success t' =>
      obtain ⟨_, _, _, _, hits⟩ := hsim
      exact ⟨_, hits q' hq'⟩

/-- The body of every item evaluates on every source word. -/
theorem body_total (hne : ∀ a, hom.letterImage a ≠ []) (total : g.IsLoffTotal)
    {x : Item Source Target m} (hx : x ∈ items hom g) (u : List Source) :
    ∃ R, (grammar hom g).Evaluates (body hom g x) u R := by
  obtain ⟨R, h⟩ := N_total hom g hne total hx u
  cases h with
  | nonterminal hb =>
      rw [rule_code hom g hx] at hb
      exact ⟨R, hb⟩

/-- Every nonterminal of the simulating grammar evaluates on every source word. -/
theorem nonterminal_total (hne : ∀ a, hom.letterImage a ≠ []) (total : g.IsLoffTotal)
    (j : Fin (count hom g)) (u : List Source) :
    ∃ R, (grammar hom g).Evaluates (.nonterminal j) u R := by
  by_cases hj : j.val < (items hom g).length
  · have hrule : (grammar hom g).rule j = body hom g (items hom g)[j.val] := by
      simp [grammar, hj]
    obtain ⟨R, h⟩ := body_total hom g hne total (List.getElem_mem hj) u
    exact ⟨R, .nonterminal (by rw [hrule]; exact h)⟩
  · have hrule : (grammar hom g).rule j = .failure := by
      simp [grammar, hj]
    exact ⟨.failure, .nonterminal (by rw [hrule]; exact .failure u)⟩

/-- **Totality.** The simulating grammar of a total grammar is total. -/
theorem grammar_isLoffTotal (hne : ∀ a, hom.letterImage a ≠ []) (total : g.IsLoffTotal) :
    (grammar hom g).IsLoffTotal :=
  PartialTotalityHelpers.loffTotal_of_nonterminal_total (nonterminal_total hom g hne total)

/-- The image is exhausted only at a boundary with the source exhausted. -/
theorem img_eq_nil (hne : ∀ a, hom.letterImage a ≠ []) {q : St Source} {u : List Source}
    (hq : q ∈ stList hom) (h : img hom q u = []) : q = none ∧ u = [] := by
  rcases q with _ | ⟨a, i⟩
  · refine ⟨rfl, ?_⟩
    cases u with
    | nil => rfl
    | cons b u =>
        simp only [img, WordHom.extend_cons, List.append_eq_nil_iff] at h
        exact absurd h.1 (hne b)
  · obtain ⟨_, h2⟩ := (some_mem_stList_iff hom).mp hq
    simp only [img, List.append_eq_nil_iff, List.drop_eq_nil_iff] at h
    omega

/-- The start item of the simulating grammar is an item. -/
theorem start_mem_items : (g.rule g.start, (none : St Source), (none : St Source)) ∈ items hom g :=
  (mem_items hom g).mpr ⟨rule_mem_closure g g.start, none_mem_stList hom, none_mem_stList hom⟩

/-- **Correctness.** The simulating grammar accepts a source word iff `g` accepts its image. -/
theorem recognizes_iff (hne : ∀ a, hom.letterImage a ≠ []) (total : g.IsLoffTotal)
    (u : List Source) :
    (grammar hom g).Recognizes u ↔ g.Recognizes (hom.extend u) := by
  constructor
  · intro hR
    change (grammar hom g).Evaluates (N hom g (g.rule g.start, none, none)) u (.success []) at hR
    obtain ⟨r, D⟩ := total (g.rule g.start) (hom.extend u)
    have hsim := complete hom g hne D none u (none_mem_stList hom) rfl (rule_mem_closure g g.start)
    cases r with
    | failure =>
        have := External.LoffForwardRepaired.PegGrammar.evaluates_deterministic hR
          (hsim none (none_mem_stList hom))
        cases this
    | success t' =>
        obtain ⟨q₁, u₁, _, himg, hits⟩ := hsim
        have := External.LoffForwardRepaired.PegGrammar.evaluates_deterministic hR
          (hits none (none_mem_stList hom))
        by_cases hq₁ : (none : St Source) = q₁
        · subst hq₁
          simp only [outcome, if_true, ParseResult.success.injEq] at this
          subst this
          have ht : t' = [] := by rw [← himg]; rfl
          subst ht
          exact .nonterminal D
        · simp [outcome, hq₁] at this
  · intro h
    cases h with
    | nonterminal D =>
        obtain ⟨q₁, u₁, hq₁, himg, hits⟩ :=
          complete hom g hne D none u (none_mem_stList hom) rfl (rule_mem_closure g g.start)
        obtain ⟨rfl, rfl⟩ := img_eq_nil hom hne hq₁ himg
        have hN := hits none (none_mem_stList hom)
        simp only [outcome, if_true, NFam] at hN
        exact hN

end Defs

end PegSeparation.Closure.InverseImageNonerasing

namespace PegSeparation.Closure

/-- **Inverse images under nonerasing homomorphisms.** If a total PEG recognizes `language`, a
total PEG recognizes its inverse image under every nonerasing homomorphism. -/
theorem recognizedByTotalPEG_inverseImage_nonerasing
    {Source Target : Type} [Fintype Source] [DecidableEq Source] [Fintype Target]
    [DecidableEq Target]
    (hom : PegSeparation.Closure.WordHom Source Target) (hne : ∀ a, hom.letterImage a ≠ [])
    {language : Language Target} (recognized : PegSeparation.RecognizedByTotalPEG language) :
    PegSeparation.RecognizedByTotalPEG (hom.inverseImage language) := by
  obtain ⟨m, g, total, hrec⟩ := recognized
  refine ⟨_, InverseImageNonerasing.grammar hom g,
    InverseImageNonerasing.grammar_isLoffTotal hom g hne total, fun w => ?_⟩
  rw [InverseImageNonerasing.recognizes_iff hom g hne total w, hrec]
  rfl

end PegSeparation.Closure

#print axioms PegSeparation.Closure.recognizedByTotalPEG_inverseImage_nonerasing
