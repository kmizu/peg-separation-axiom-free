import PegSeparation.CFLNotPEG.External.LoffForwardRepaired
import PegSeparation.Common.Compiler.SCAToPEG.Final


namespace PegSeparation.Closure

open PegSeparation
open PegSeparation.Scaffolding

namespace LeftRegularConcat

variable {Terminal : Type} {stateCount workLabelCount degree radius : Nat}
variable {σ : Type} [Fintype σ] [DecidableEq σ]


private def liveStep (D : DFA Terminal σ) (live : Finset σ) (symbol : Terminal)
    (accepted : Prop) [Decidable accepted] : Finset σ :=
  live.image (fun state => D.step state symbol) ∪ (if accepted then {D.start} else ∅)

omit [Fintype σ] in
private theorem mem_liveStep (D : DFA Terminal σ) (live : Finset σ) (symbol : Terminal)
    (accepted : Prop) [Decidable accepted] (target : σ) :
    target ∈ liveStep D live symbol accepted ↔
      (∃ source ∈ live, D.step source symbol = target) ∨
        (accepted ∧ target = D.start) := by
  unfold liveStep
  by_cases h : accepted
  · rw [if_pos h]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton, and_iff_right h]
  · rw [if_neg h]
    simp only [Finset.union_empty, Finset.mem_image, h, false_and, or_false]


private abbrev ProductCard (stateCount : Nat) (σ : Type) [Fintype σ] : Nat :=
  Fintype.card (Fin stateCount × Finset σ)

private noncomputable def code (stateCount : Nat) (σ : Type) [Fintype σ] :
    Fin stateCount × Finset σ ≃ Fin (ProductCard stateCount σ) :=
  Fintype.equivFin _

private def productAction
    (A : Automaton Terminal stateCount workLabelCount degree radius)
    (D : DFA Terminal σ) (state : Fin stateCount) (live : Finset σ)
    (symbol : Terminal) (view : Neighborhood (Fin workLabelCount) degree radius) :
    Action (Fin stateCount × Finset σ) (Fin workLabelCount) degree radius where
  nextState :=
    ((A.transition state symbol view).nextState,
      liveStep D live symbol ((A.transition state symbol view).nextState ∈ A.accepting))
  newLabel := (A.transition state symbol view).newLabel
  target := (A.transition state symbol view).target

private noncomputable def product
    (A : Automaton Terminal stateCount workLabelCount degree radius)
    (D : DFA Terminal σ) :
    Automaton Terminal (ProductCard stateCount σ) workLabelCount degree radius where
  degreePositive := A.degreePositive
  initialState :=
    code stateCount σ
      (A.initialState, if A.initialState ∈ A.accepting then {D.start} else ∅)
  accepting :=
    @Finset.filter (Fin (ProductCard stateCount σ))
      (fun index => ∃ state ∈ ((code stateCount σ).symm index).2, state ∈ D.accept)
      (fun _ => Classical.dec _) Finset.univ
  transition := fun index symbol view =>
    { nextState :=
        code stateCount σ
          (productAction A D ((code stateCount σ).symm index).1
            ((code stateCount σ).symm index).2 symbol view).nextState
      newLabel :=
        (productAction A D ((code stateCount σ).symm index).1
          ((code stateCount σ).symm index).2 symbol view).newLabel
      target :=
        (productAction A D ((code stateCount σ).symm index).1
          ((code stateCount σ).symm index).2 symbol view).target }

private theorem mem_product_accepting
    (A : Automaton Terminal stateCount workLabelCount degree radius)
    (D : DFA Terminal σ) (index : Fin (ProductCard stateCount σ)) :
    index ∈ (product A D).accepting ↔
      ∃ state ∈ ((code stateCount σ).symm index).2, state ∈ D.accept := by
  simp [product]


private theorem run_append
    (M : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) (symbol : Terminal) :
    M.run (input ++ [symbol]) = M.step (M.run input) symbol := by
  simp [Automaton.run]

private theorem step_eq (M : Automaton Terminal stateCount workLabelCount degree radius)
    (state : Fin stateCount) (scaffold : Scaffold (Fin workLabelCount) degree)
    (symbol : Terminal) :
    M.step (state, scaffold) symbol =
      ((M.transition state symbol (scaffold.topNeighborhood radius)).nextState,
        Automaton.extendScaffold scaffold
          (M.transition state symbol (scaffold.topNeighborhood radius))) :=
  rfl

private theorem step_product
    (A : Automaton Terminal stateCount workLabelCount degree radius)
    (D : DFA Terminal σ) (index : Fin (ProductCard stateCount σ))
    (state : Fin stateCount) (scaffold : Scaffold (Fin workLabelCount) degree)
    (symbol : Terminal) (hstate : ((code stateCount σ).symm index).1 = state) :
    (product A D).step (index, scaffold) symbol =
      (code stateCount σ
        (productAction A D state ((code stateCount σ).symm index).2 symbol
          (scaffold.topNeighborhood radius)).nextState,
        (A.step (state, scaffold) symbol).2) := by
  subst hstate
  rfl


private theorem run_product
    (A : Automaton Terminal stateCount workLabelCount degree radius)
    (D : DFA Terminal σ) (L : Language Terminal)
    (hA : ∀ input, A.Accepts input ↔ input ∈ L)
    (input : List Terminal) :
    ((code stateCount σ).symm ((product A D).run input).1).1 = (A.run input).1 ∧
      ((product A D).run input).2 = (A.run input).2 ∧
        ∀ target : σ,
          target ∈ ((code stateCount σ).symm ((product A D).run input).1).2 ↔
            ∃ before after, input = before ++ after ∧ before ∈ L ∧
              D.evalFrom D.start after = target := by
  induction input using List.reverseRecOn with
  | nil =>
      have hnil : A.initialState ∈ A.accepting ↔ [] ∈ L := by
        have := hA []
        simpa [Automaton.Accepts, Automaton.run] using this
      refine ⟨by simp [Automaton.run, product], by simp [Automaton.run, product], ?_⟩
      intro target
      simp only [Automaton.run, List.foldl_nil, product, Equiv.symm_apply_apply]
      constructor
      · intro hmem
        by_cases hacc : A.initialState ∈ A.accepting
        · rw [if_pos hacc, Finset.mem_singleton] at hmem
          exact ⟨[], [], rfl, hnil.mp hacc, hmem.symm⟩
        · rw [if_neg hacc] at hmem
          exact absurd hmem (Finset.notMem_empty target)
      · rintro ⟨before, after, hsplit, hbefore, heval⟩
        obtain ⟨rfl, rfl⟩ : before = [] ∧ after = [] :=
          List.append_eq_nil_iff.mp hsplit.symm
        rw [if_pos (hnil.mpr hbefore), Finset.mem_singleton]
        exact heval.symm
  | append_singleton previous symbol ih =>
      obtain ⟨hcontrol, hscaffold, hlive⟩ := ih
      have hrunProduct : (product A D).run (previous ++ [symbol]) =
          (product A D).step (((product A D).run previous).1, (A.run previous).2) symbol := by
        rw [run_append, ← hscaffold]
      have hrunBase : A.run (previous ++ [symbol]) =
          A.step ((A.run previous).1, (A.run previous).2) symbol := run_append A previous symbol
      have haccept :
          (A.transition (A.run previous).1 symbol
              ((A.run previous).2.topNeighborhood radius)).nextState ∈ A.accepting ↔
            previous ++ [symbol] ∈ L := by
        rw [← hA (previous ++ [symbol])]
        change _ ↔ (A.run (previous ++ [symbol])).1 ∈ A.accepting
        rw [hrunBase]
        exact Iff.rfl
      rw [hrunProduct, step_product A D _ (A.run previous).1 _ symbol hcontrol, hrunBase,
        step_eq]
      refine ⟨by simp [productAction], rfl, ?_⟩
      intro target
      simp only [productAction, Equiv.symm_apply_apply]
      rw [mem_liveStep, haccept]
      constructor
      · rintro (⟨source, hsource, hstep⟩ | ⟨hmem, htarget⟩)
        · obtain ⟨before, after, hsplit, hbefore, heval⟩ := (hlive source).mp hsource
          refine ⟨before, after ++ [symbol], ?_, hbefore, ?_⟩
          · rw [hsplit, List.append_assoc]
          · rw [DFA.evalFrom_append_singleton, heval, hstep]
        · exact ⟨previous ++ [symbol], [], (List.append_nil _).symm, hmem, htarget.symm⟩
      · rintro ⟨before, after, hsplit, hbefore, heval⟩
        cases after using List.reverseRecOn with
        | nil =>
            rw [List.append_nil] at hsplit
            exact Or.inr ⟨hsplit ▸ hbefore, heval.symm⟩
        | append_singleton middle last =>
            rw [← List.append_assoc] at hsplit
            obtain ⟨hprevious, hlast⟩ :=
              List.append_inj' hsplit.symm (by simp)
            have hlast' : last = symbol := by simpa using hlast
            subst hlast'
            refine Or.inl ⟨D.evalFrom D.start middle, (hlive _).mpr
              ⟨before, middle, hprevious.symm, hbefore, rfl⟩, ?_⟩
            rw [← heval, DFA.evalFrom_append_singleton]

private theorem accepts_product
    (A : Automaton Terminal stateCount workLabelCount degree radius)
    (D : DFA Terminal σ) (L : Language Terminal)
    (hA : ∀ input, A.Accepts input ↔ input ∈ L)
    (input : List Terminal) :
    (product A D).Accepts input ↔ input ∈ L * D.accepts := by
  obtain ⟨-, -, hlive⟩ := run_product A D L hA input
  simp only [Automaton.Accepts, mem_product_accepting]
  constructor
  · rintro ⟨state, hstate, haccept⟩
    obtain ⟨before, after, rfl, hbefore, rfl⟩ := (hlive state).mp hstate
    exact Language.mem_mul.mpr ⟨before, hbefore, after, haccept, rfl⟩
  · intro hmem
    obtain ⟨before, hbefore, after, hafter, rfl⟩ := Language.mem_mul.mp hmem
    exact ⟨D.evalFrom D.start after, (hlive _).mpr ⟨before, after, rfl, hbefore, rfl⟩, hafter⟩

end LeftRegularConcat

set_option linter.unusedFintypeInType false in
theorem recognizedByTotalPEG_mul_of_isRegular_left
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    {R Y : Language Terminal} (hR : R.IsRegular)
    (hY : PegSeparation.RecognizedByTotalPEG Y) :
    PegSeparation.RecognizedByTotalPEG (R * Y) := by
  obtain ⟨nonterminalCount, grammar, htotal, hgrammar⟩ := hY
  obtain ⟨stateCount, workLabelCount, degree, radius, A, hA⟩ :=
    PegSeparation.External.LoffForwardRepaired.loffForwardStatement grammar htotal
  obtain ⟨σ, σfintype, D, hD⟩ := hR.reverse
  haveI : Fintype σ := σfintype
  haveI : DecidableEq σ := Classical.decEq σ
  have hAreverse : ∀ input, A.Accepts input ↔ input ∈ Y.reverse := fun input =>
    (hA input).trans (hgrammar input.reverse)
  obtain ⟨productNonterminalCount, productGrammar, hproductTotal, hproductRecognizes⟩ :=
    PegSeparation.SCAToPEG.loffBackward (LeftRegularConcat.product A D)
  refine ⟨productNonterminalCount, productGrammar, hproductTotal, fun word => ?_⟩
  have hword := hproductRecognizes word.reverse
  rw [List.reverse_reverse] at hword
  rw [← hword, LeftRegularConcat.accepts_product A D Y.reverse hAreverse, hD,
    ← Language.reverse_mul R Y]
  exact Language.reverse_mem_reverse

end PegSeparation.Closure
