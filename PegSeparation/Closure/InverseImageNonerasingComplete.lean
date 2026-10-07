import PegSeparation.Closure.InverseImageNonerasingBasic

/-!
# Inverse images under nonerasing homomorphisms: the simulation is complete

`complete`: whenever `g` evaluates a subexpression `e` on the image `img q u`, the calls
`N (e, q, q')` of the simulating grammar all evaluate on `u`, and their results mirror the
original one: if `e` fails, every call fails; if `e` succeeds with rest `t'`, there is one end
state `q₁` (with source rest `u₁`, `img q₁ u₁ = t'`) whose call succeeds with `u₁`, and every other
call fails.
-/

set_option linter.unusedSectionVars false

namespace PegSeparation.Closure.InverseImageNonerasing

open PegSeparation PegSeparation.PegGrammar

section Defs

variable {Source Target : Type} [Fintype Source] [DecidableEq Source] [DecidableEq Target]
  {m : ℕ}

variable (hom : WordHom Source Target) (g : PegGrammar Target m)

/-- The calls of `e` from `q`, indexed by the end state. -/
noncomputable def NFam (e : ParsingExpression Target m) (q : St Source) :
    St Source → ParsingExpression Source (count hom g) :=
  fun q' => N hom g (e, q, q')

/-- A family of end-state calls, evaluated on `u`, **simulates** the original result. -/
def SimF (F : St Source → ParsingExpression Source (count hom g)) (u : List Source) :
    ParseResult Target → Prop
  | .failure => ∀ q' ∈ stList hom, (grammar hom g).Evaluates (F q') u .failure
  | .success t' => ∃ q₁ u₁, q₁ ∈ stList hom ∧ img hom q₁ u₁ = t' ∧
      ∀ q' ∈ stList hom, (grammar hom g).Evaluates (F q') u (outcome q₁ u₁ q')

/-- Unfolding `SimF` at failure. -/
theorem SimF_failure {F : St Source → ParsingExpression Source (count hom g)} {u : List Source} :
    SimF hom g F u .failure ↔ ∀ q' ∈ stList hom, (grammar hom g).Evaluates (F q') u .failure :=
  Iff.rfl

/-- Unfolding `SimF` at success. -/
theorem SimF_success {F : St Source → ParsingExpression Source (count hom g)} {u : List Source}
    {t' : List Target} :
    SimF hom g F u (.success t') ↔ ∃ q₁ u₁, q₁ ∈ stList hom ∧ img hom q₁ u₁ = t' ∧
      ∀ q' ∈ stList hom, (grammar hom g).Evaluates (F q') u (outcome q₁ u₁ q') :=
  Iff.rfl

/-- Simulation transfers along member-wise implications of evaluations. -/
theorem SimF_mono {F F' : St Source → ParsingExpression Source (count hom g)}
    {u u' : List Source} {r : ParseResult Target} (h : SimF hom g F u r)
    (hFF : ∀ q' ∈ stList hom, ∀ R, (grammar hom g).Evaluates (F q') u R →
      (grammar hom g).Evaluates (F' q') u' R) :
    SimF hom g F' u' r := by
  cases r with
  | failure => exact fun q' hq' => hFF q' hq' _ (h q' hq')
  | success t' =>
      obtain ⟨q₁, u₁, hq₁, himg, hits⟩ := h
      exact ⟨q₁, u₁, hq₁, himg, fun q' hq' => hFF q' hq' _ (hits q' hq')⟩

/-- Evaluating a terminal on a nonempty input. -/
theorem terminal_eval_cons {n : ℕ} {G : PegGrammar Source n} (a b : Source)
    (u : List Source) :
    G.Evaluates (.terminal a) (b :: u) (if b = a then .success u else .failure) := by
  have := Evaluates.terminal (grammar := G) a (b :: u)
  by_cases h : b = a <;> simpa [terminalResult, h] using this

/-- The letter test at a boundary fails on the empty source. -/
theorem step1_none_nil (c : Target) (q' : St Source) :
    (grammar hom g).Evaluates (step1 hom g c none q') [] .failure := by
  refine chain_fail (fun a _ => ?_)
  split_ifs
  · exact Evaluates.terminal a []
  · exact .failure []

/-- The letter test at a boundary on `b :: u`, when the block of `b` starts with `c`. -/
theorem step1_none_cons_hit (c : Target) {b : Source} {u : List Source}
    (hb : (hom.letterImage b)[0]? = some c) (q' : St Source) :
    (grammar hom g).Evaluates (step1 hom g c none q') (b :: u)
      (outcome (nextSt hom b 0) u q') := by
  refine chain_pick (y₁ := b) (mem_letters b) ?_ (fun a _ hab => ?_)
  · by_cases hq : q' = nextSt hom b 0
    · rw [if_pos ⟨hb, hq.symm⟩]
      simpa [outcome, hq] using terminal_eval_cons (G := grammar hom g) b b u
    · rw [if_neg (fun h => hq h.2.symm)]
      simpa [outcome, hq] using Evaluates.failure (grammar := grammar hom g) (b :: u)
  · split_ifs
    · simpa [Ne.symm hab] using terminal_eval_cons (G := grammar hom g) a b u
    · exact .failure _

/-- The letter test at a boundary on `b :: u`, when the block of `b` does not start with `c`. -/
theorem step1_none_cons_miss (c : Target) {b : Source} {u : List Source}
    (hb : (hom.letterImage b)[0]? ≠ some c) (q' : St Source) :
    (grammar hom g).Evaluates (step1 hom g c none q') (b :: u) .failure := by
  refine chain_fail (fun a _ => ?_)
  by_cases hab : a = b
  · subst hab
    rw [if_neg (fun h => hb h.1)]
    exact .failure _
  · split_ifs
    · simpa [Ne.symm hab] using terminal_eval_cons (G := grammar hom g) a b u
    · exact .failure _

/-- The terminal case of completeness. -/
theorem sim_terminal (hne : ∀ a, hom.letterImage a ≠ []) (c : Target) {q : St Source}
    (hq : q ∈ stList hom) (u : List Source)
    (he : (.terminal c : ParsingExpression Target m) ∈ closure g) :
    SimF hom g (NFam hom g (.terminal c) q) u (terminalResult c (img hom q u)) := by
  have hmem : ∀ q' ∈ stList hom,
      ((.terminal c : ParsingExpression Target m), q, q') ∈ items hom g :=
    fun q' hq' => (mem_items hom g).mpr ⟨he, hq, hq'⟩
  rcases q with _ | ⟨a, i⟩
  · cases u with
    | nil =>
        show SimF hom g _ [] .failure
        exact fun q' hq' => N_eval hom g (hmem q' hq') (step1_none_nil hom g c q')
    | cons b u =>
        obtain ⟨d, rest, hdr⟩ := List.exists_cons_of_ne_nil (hne b)
        have hpos : 0 < (hom.letterImage b).length := by simp [hdr]
        have himg : img hom none (b :: u) = d :: (rest ++ hom.extend u) := by
          simp [img, hdr]
        have himg' : img hom (nextSt hom b 0) u = rest ++ hom.extend u := by
          rw [img_nextSt hom hpos u, hdr]; simp
        have hget : (hom.letterImage b)[0]? = some d := by simp [hdr]
        rw [himg]
        by_cases hdc : d = c
        · simp only [terminalResult, hdc, if_true]
          refine ⟨nextSt hom b 0, u, nextSt_mem hom, himg', ?_⟩
          exact fun q' hq' => N_eval hom g (hmem q' hq')
            (step1_none_cons_hit hom g c (by rw [hget, hdc]) q')
        · simp only [terminalResult, hdc, if_false]
          exact fun q' hq' => N_eval hom g (hmem q' hq')
            (step1_none_cons_miss hom g c (by rw [hget]; simpa using hdc) q')
  · obtain ⟨h1, h2⟩ := (some_mem_stList_iff hom).mp hq
    have himg : img hom (some (a, i)) u =
        (hom.letterImage a)[i] :: ((hom.letterImage a).drop (i + 1) ++ hom.extend u) := by
      simp only [img]
      rw [show (hom.letterImage a).drop i = _ :: _ from drop_eq_getElem_cons h2]
      rfl
    have hget : (hom.letterImage a)[i]? = some (hom.letterImage a)[i] :=
      List.getElem?_eq_getElem h2
    rw [himg]
    by_cases hdc : (hom.letterImage a)[i] = c
    · simp only [terminalResult, hdc, if_true]
      refine ⟨nextSt hom a i, u, nextSt_mem hom, img_nextSt hom h2 u, fun q' hq' => ?_⟩
      refine N_eval hom g (hmem q' hq') ?_
      have hres : outcome (nextSt hom a i) u q' =
          if ((hom.letterImage a)[i]? = some c ∧ nextSt hom a i = q')
          then .success u else .failure := by
        by_cases hq' : q' = nextSt hom a i
        · simp [outcome, hq', hget, hdc]
        · simp [outcome, hq', Ne.symm hq']
      rw [hres]
      exact ite_eval _ u
    · simp only [terminalResult, hdc, if_false]
      refine fun q' hq' => N_eval hom g (hmem q' hq') ?_
      show (grammar hom g).Evaluates
        (if (hom.letterImage a)[i]? = some c ∧ nextSt hom a i = q' then .empty else .failure)
        u .failure
      rw [if_neg (fun h => hdc (by rw [hget] at h; simpa using h.1))]
      exact .failure u

/-- **Completeness of the simulation.** If `g` evaluates `e` on `img q u` to `r`, the calls of
`e` from `q` on `u` simulate `r`. -/
theorem complete (hne : ∀ a, hom.letterImage a ≠ []) {e : ParsingExpression Target m}
    {t : List Target} {r : ParseResult Target} (D : g.Evaluates e t r) :
    ∀ q u, q ∈ stList hom → img hom q u = t → e ∈ closure g →
      SimF hom g (NFam hom g e q) u r := by
  induction D with
  | empty input =>
      intro q u hq himg he
      exact ⟨q, u, hq, himg, fun q' hq' =>
        N_eval hom g ((mem_items hom g).mpr ⟨he, hq, hq'⟩) (guardEq_eval q q' u)⟩
  | failure input =>
      intro q u hq _ he q' hq'
      exact N_eval hom g ((mem_items hom g).mpr ⟨he, hq, hq'⟩) (.failure u)
  | terminal symbol input =>
      intro q u hq himg he
      subst himg
      exact sim_terminal hom g hne symbol hq u he
  | @nonterminal name input result _ ih =>
      intro q u hq himg he
      refine SimF_mono hom g (ih q u hq himg (rule_mem_closure g name)) (fun q' hq' R h => ?_)
      exact N_eval hom g ((mem_items hom g).mpr ⟨he, hq, hq'⟩) h
  | @sequenceFailure e₁ e₂ input _ ih =>
      intro q u hq himg he q' hq'
      have h₁ := ih q u hq himg (closure_sub g he (by simp [subs, self_mem_subs]))
      exact N_eval hom g ((mem_items hom g).mpr ⟨he, hq, hq'⟩)
        (chain_fail (fun y hy => .sequenceFailure (h₁ y hy)))
  | @sequenceSuccess e₁ e₂ input middle result _ _ ih₁ ih₂ =>
      intro q u hq himg he
      obtain ⟨y₁, u₁, hy₁, himg₁, hits₁⟩ :=
        ih₁ q u hq himg (closure_sub g he (by simp [subs, self_mem_subs]))
      have h₂ := ih₂ y₁ u₁ hy₁ himg₁ (closure_sub g he (by simp [subs, self_mem_subs]))
      refine SimF_mono hom g h₂ (fun q' hq' R h => ?_)
      refine N_eval hom g ((mem_items hom g).mpr ⟨he, hq, hq'⟩) ?_
      refine chain_pick hy₁ (.sequenceSuccess (by simpa [outcome, NFam] using hits₁ y₁ hy₁) h)
        (fun y hy hne => .sequenceFailure (by simpa [outcome, hne, NFam] using hits₁ y hy))
  | @choiceLeft e₁ e₂ input remaining _ ih =>
      intro q u hq himg he
      obtain ⟨q₁, u₁, hq₁, himg₁, hits₁⟩ :=
        ih q u hq himg (closure_sub g he (by simp [subs, self_mem_subs]))
      refine ⟨q₁, u₁, hq₁, himg₁, fun q' hq' => ?_⟩
      refine N_eval hom g ((mem_items hom g).mpr ⟨he, hq, hq'⟩) ?_
      by_cases hq'₁ : q' = q₁
      · subst hq'₁
        have h₁ := hits₁ q' hq'
        simp only [outcome] at h₁ ⊢
        exact .choiceLeft h₁
      · simp only [outcome, if_neg hq'₁]
        exact .choiceRight (by simpa [outcome, hq'₁, NFam] using hits₁ q' hq')
          (.sequenceFailure (.notFailure (chain_hits hq₁ hits₁)))
  | @choiceRight e₁ e₂ input result _ _ ih₁ ih₂ =>
      intro q u hq himg he
      have h₁ := ih₁ q u hq himg (closure_sub g he (by simp [subs, self_mem_subs]))
      have h₂ := ih₂ q u hq himg (closure_sub g he (by simp [subs, self_mem_subs]))
      refine SimF_mono hom g h₂ (fun q' hq' R h => ?_)
      exact N_eval hom g ((mem_items hom g).mpr ⟨he, hq, hq'⟩)
        (.choiceRight (h₁ q' hq') (.sequenceSuccess (.notSuccess (chain_fail h₁)) h))
  | @notSuccess e₁ input _ ih =>
      intro q u hq himg he
      have h₁ := ih q u hq himg (closure_sub g he (by simp [subs, self_mem_subs]))
      exact ⟨q, u, hq, himg, fun q' hq' => N_eval hom g ((mem_items hom g).mpr ⟨he, hq, hq'⟩)
        (.sequenceSuccess (.notSuccess (chain_fail h₁)) (guardEq_eval q q' u))⟩
  | @notFailure e₁ input remaining _ ih =>
      intro q u hq himg he q' hq'
      obtain ⟨q₁, u₁, hq₁, _, hits₁⟩ :=
        ih q u hq himg (closure_sub g he (by simp [subs, self_mem_subs]))
      exact N_eval hom g ((mem_items hom g).mpr ⟨he, hq, hq'⟩)
        (.sequenceFailure (.notFailure (chain_hits hq₁ hits₁)))
  | @andSuccess e₁ input remaining _ ih =>
      intro q u hq himg he
      obtain ⟨q₁, u₁, hq₁, _, hits₁⟩ :=
        ih q u hq himg (closure_sub g he (by simp [subs, self_mem_subs]))
      exact ⟨q, u, hq, himg, fun q' hq' => N_eval hom g ((mem_items hom g).mpr ⟨he, hq, hq'⟩)
        (.sequenceSuccess (.andSuccess (chain_hits hq₁ hits₁)) (guardEq_eval q q' u))⟩
  | @andFailure e₁ input _ ih =>
      intro q u hq himg he q' hq'
      have h₁ := ih q u hq himg (closure_sub g he (by simp [subs, self_mem_subs]))
      exact N_eval hom g ((mem_items hom g).mpr ⟨he, hq, hq'⟩)
        (.sequenceFailure (.andFailure (chain_fail h₁)))

end Defs

end PegSeparation.Closure.InverseImageNonerasing
