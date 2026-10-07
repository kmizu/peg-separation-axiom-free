import PegSeparation.Common.Loff.Semantics


namespace PegSeparation.External.LoffForwardRepaired

open PegSeparation


inductive SameInputCall
    {Terminal : Type} [DecidableEq Terminal] {nonterminalCount : Nat}
    (grammar : PegGrammar Terminal nonterminalCount)
    (total : grammar.IsLoffTotal)
    (input : List Terminal) :
    ParsingExpression Terminal nonterminalCount →
      ParsingExpression Terminal nonterminalCount → Prop
  | nonterminal (name) :
      SameInputCall grammar total input (grammar.rule name) (.nonterminal name)
  | sequenceLeft (left right) :
      SameInputCall grammar total input left (.sequence left right)
  | sequenceRight (left right)
      (leftZero : Semantic.status grammar total left input = .zero) :
      SameInputCall grammar total input right (.sequence left right)
  | choiceLeft (left right) :
      SameInputCall grammar total input left (.orderedChoice left right)
  | choiceRight (left right)
      (leftFails : Semantic.status grammar total left input = .failure) :
      SameInputCall grammar total input right (.orderedChoice left right)
  | notBody (body) :
      SameInputCall grammar total input body (.notPredicate body)
  | andBody (body) :
      SameInputCall grammar total input body (.andPredicate body)

namespace SameInputCall

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
  {nonterminalCount : Nat}
  (grammar : PegGrammar Terminal nonterminalCount)
  (total : grammar.IsLoffTotal)
  (input : List Terminal)

theorem acc_of_evaluates
    {expression : ParsingExpression Terminal nonterminalCount}
    {parseResult : ParseResult Terminal}
    (evaluation : grammar.Evaluates expression input parseResult) :
    Acc (SameInputCall grammar total input) expression := by
  induction evaluation with
  | empty =>
      refine Acc.intro _ ?_
      intro child call
      cases call
  | failure =>
      refine Acc.intro _ ?_
      intro child call
      cases call
  | terminal =>
      refine Acc.intro _ ?_
      intro child call
      cases call
  | nonterminal body ih =>
      refine Acc.intro _ ?_
      intro child call
      cases call
      exact ih
  | sequenceFailure leftFails ih =>
      refine Acc.intro _ ?_
      intro child call
      cases call with
      | sequenceLeft => exact ih
      | sequenceRight left right leftZero =>
          have leftFailure :=
            (Semantic.status_eq_failure_iff grammar total _ _).mpr
              (Semantic.result_eq_of_evaluates grammar total leftFails)
          have impossible : Status.failure = Status.zero := leftFailure.symm.trans leftZero
          cases impossible
  | sequenceSuccess leftSucceeds rightResult ihLeft ihRight =>
      refine Acc.intro _ ?_
      intro child call
      cases call with
      | sequenceLeft => exact ihLeft
      | sequenceRight left right leftZero =>
          have resultAtMiddle :=
            Semantic.result_eq_of_evaluates grammar total leftSucceeds
          have resultAtInput :=
            (Semantic.status_eq_zero_iff grammar total _ _).mp leftZero
          have middleEq :=
            ParseResult.success.inj (resultAtMiddle.symm.trans resultAtInput)
          cases middleEq
          exact ihRight
  | choiceLeft leftSucceeds ih =>
      refine Acc.intro _ ?_
      intro child call
      cases call with
      | choiceLeft => exact ih
      | choiceRight left right leftFails =>
          have resultSuccess :=
            Semantic.result_eq_of_evaluates grammar total leftSucceeds
          have resultFailure :=
            (Semantic.status_eq_failure_iff grammar total _ _).mp leftFails
          have impossible := resultSuccess.symm.trans resultFailure
          cases impossible
  | choiceRight leftFails rightResult ihLeft ihRight =>
      refine Acc.intro _ ?_
      intro child call
      cases call with
      | choiceLeft => exact ihLeft
      | choiceRight => exact ihRight
  | notSuccess bodyFails ih =>
      refine Acc.intro _ ?_
      intro child call
      cases call
      exact ih
  | notFailure bodySucceeds ih =>
      refine Acc.intro _ ?_
      intro child call
      cases call
      exact ih
  | andSuccess bodySucceeds ih =>
      refine Acc.intro _ ?_
      intro child call
      cases call
      exact ih
  | andFailure bodyFails ih =>
      refine Acc.intro _ ?_
      intro child call
      cases call
      exact ih

theorem wellFounded :
    WellFounded (SameInputCall grammar total input) :=
  WellFounded.intro fun expression =>
    acc_of_evaluates grammar total input
      (Semantic.result_spec grammar total expression input)

theorem preserves_relevant
    {child parent : ParsingExpression Terminal nonterminalCount}
    (call : SameInputCall grammar total input child parent)
    (parentRelevant : parent ∈ relevantExpressions grammar) :
    child ∈ relevantExpressions grammar := by
  cases call with
  | nonterminal name => exact rule_mem_relevantExpressions grammar name
  | sequenceLeft left right =>
      exact subexpression_mem_relevantExpressions grammar parentRelevant
        (by simp [subexpressions])
  | sequenceRight left right leftZero =>
      exact subexpression_mem_relevantExpressions grammar parentRelevant
        (by simp [subexpressions])
  | choiceLeft left right =>
      exact subexpression_mem_relevantExpressions grammar parentRelevant
        (by simp [subexpressions])
  | choiceRight left right leftFails =>
      exact subexpression_mem_relevantExpressions grammar parentRelevant
        (by simp [subexpressions])
  | notBody body =>
      exact subexpression_mem_relevantExpressions grammar parentRelevant
        (by simp [subexpressions])
  | andBody body =>
      exact subexpression_mem_relevantExpressions grammar parentRelevant
        (by simp [subexpressions])

end SameInputCall



def CallBound {α : Type} (relation : α → α → Prop) :
    Nat → α → Prop
  | 0, _ => False
  | fuel + 1, point =>
      ∀ child, relation child point → CallBound relation fuel child

theorem CallBound.mono {α : Type} {relation : α → α → Prop}
    {point : α} {small large : Nat} (hle : small ≤ large) :
    CallBound relation small point → CallBound relation large point := by
  induction large generalizing small point with
  | zero =>
      have hsmall : small = 0 := Nat.eq_zero_of_le_zero hle
      subst small
      exact id
  | succ large ih =>
      cases small with
      | zero => simp [CallBound]
      | succ small =>
          intro bound
          rw [CallBound] at bound ⊢
          intro child edge
          exact ih (Nat.le_of_succ_le_succ hle) (bound child edge)

theorem exists_callBound_of_acc {α : Type} [Fintype α]
    {relation : α → α → Prop} {point : α}
    (accessible : Acc relation point) :
    ∃ fuel, CallBound relation fuel point := by
  classical
  induction accessible with
  | intro point predecessors ih =>
      let childFuel : α → Nat := fun child =>
        if edge : relation child point then Classical.choose (ih child edge) else 0
      refine ⟨Finset.univ.sup childFuel + 1, ?_⟩
      rw [CallBound]
      intro child edge
      apply CallBound.mono (Finset.le_sup (f := childFuel) (Finset.mem_univ child))
      dsimp [childFuel]
      rw [dif_pos edge]
      exact Classical.choose_spec (ih child edge)

theorem exists_uniform_callBound {α : Type} [Fintype α]
    {relation : α → α → Prop} (wellFounded : WellFounded relation) :
    ∃ fuel, ∀ point, CallBound relation fuel point := by
  classical
  let pointFuel : α → Nat := fun point =>
    Classical.choose (exists_callBound_of_acc (wellFounded.apply point))
  refine ⟨Finset.univ.sup pointFuel, ?_⟩
  intro point
  apply CallBound.mono (Finset.le_sup (f := pointFuel) (Finset.mem_univ point))
  exact Classical.choose_spec (exists_callBound_of_acc (wellFounded.apply point))

noncomputable def booleanRelationBound {α : Type} [Fintype α]
    (matrix : α → α → Bool) : Nat := by
  classical
  exact
    if wellFounded : WellFounded (fun child point => matrix child point = true) then
      Classical.choose (exists_uniform_callBound wellFounded)
    else
      0

theorem booleanRelationBound_spec {α : Type} [Fintype α]
    (matrix : α → α → Bool)
    (wellFounded : WellFounded (fun child point => matrix child point = true)) :
    ∀ point, CallBound (fun child parent => matrix child parent = true)
      (booleanRelationBound matrix) point := by
  classical
  rw [booleanRelationBound, dif_pos wellFounded]
  exact Classical.choose_spec (exists_uniform_callBound wellFounded)

end PegSeparation.External.LoffForwardRepaired
