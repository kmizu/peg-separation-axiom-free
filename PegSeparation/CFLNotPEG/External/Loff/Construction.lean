import PegSeparation.CFLNotPEG.External.Loff.Termination


namespace PegSeparation.External.LoffForwardRepaired

open PegSeparation


namespace Construction

variable {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
  {nonterminalCount : Nat}
  (grammar : PegGrammar Terminal nonterminalCount)
  (total : grammar.IsLoffTotal)

private noncomputable instance constructionExpressionDecidableEq :
    DecidableEq (ParsingExpression Terminal nonterminalCount) := Classical.decEq _

noncomputable abbrev Degree : Nat := Fintype.card (Coordinate grammar) + 1

noncomputable abbrev WorkLabel :=
  Coordinate grammar → Status

noncomputable abbrev WorkLabelCount : Nat :=
  Fintype.card (WorkLabel grammar)

noncomputable def callMatrix (input : List Terminal) :
    Coordinate grammar → Coordinate grammar → Bool := by
  classical
  exact fun child parent =>
    decide (SameInputCall grammar total input child.1 parent.1)

theorem callMatrix_wellFounded (input : List Terminal) :
    WellFounded (fun child parent => callMatrix grammar total input child parent = true) := by
  classical
  have restricted :=
    InvImage.wf (fun coordinate : Coordinate grammar => coordinate.1)
      (SameInputCall.wellFounded grammar total input)
  change WellFounded (fun child parent : Coordinate grammar =>
    SameInputCall grammar total input child.1 parent.1) at restricted
  simpa [callMatrix] using restricted

noncomputable def Radius : Nat :=
  Finset.univ.sup
    (fun matrix : Coordinate grammar → Coordinate grammar → Bool =>
      booleanRelationBound matrix) + 1

theorem callBound_radius (input : List Terminal) (point : Coordinate grammar) :
    CallBound
      (fun child parent : Coordinate grammar =>
        SameInputCall grammar total input child.1 parent.1)
      (Radius grammar) point := by
  classical
  let matrix := callMatrix grammar total input
  have bounded := booleanRelationBound_spec matrix
    (callMatrix_wellFounded grammar total input) point
  have hle : booleanRelationBound matrix ≤ Radius grammar := by
    dsimp [Radius]
    exact (Finset.le_sup (f := fun relation :
      Coordinate grammar → Coordinate grammar → Bool =>
        booleanRelationBound relation) (Finset.mem_univ matrix)).trans (Nat.le_succ _)
  apply CallBound.mono hle
  simpa [matrix, callMatrix] using bounded

noncomputable def coordinateEquiv :
    Coordinate grammar ≃ Fin (Fintype.card (Coordinate grammar)) :=
  Fintype.equivFin _

noncomputable def labelEquiv :
    WorkLabel grammar ≃ Fin (WorkLabelCount grammar) :=
  Fintype.equivFin _

noncomputable def direction (coordinate : Coordinate grammar) :
    Fin (Degree grammar) :=
  Fin.castSucc (coordinateEquiv grammar coordinate)

noncomputable def directionOf
    (expression : ParsingExpression Terminal nonterminalCount) :
    Fin (Degree grammar) :=
  if h : expression ∈ relevantExpressions grammar then
    direction grammar ⟨expression, h⟩
  else
    Fin.last (Fintype.card (Coordinate grammar))

noncomputable def encodeLabel (label : WorkLabel grammar) :
    Fin (WorkLabelCount grammar) :=
  labelEquiv grammar label

noncomputable def decodeLabel (label : Fin (WorkLabelCount grammar)) :
    WorkLabel grammar :=
  (labelEquiv grammar).symm label

@[simp] theorem decode_encodeLabel (label : WorkLabel grammar) :
    decodeLabel grammar (encodeLabel grammar label) = label :=
  (labelEquiv grammar).symm_apply_apply label

abbrev viewLabel {Work : Type} {degree : Nat} :
    (radius : Nat) → Scaffolding.Neighborhood Work degree radius →
      List (Fin degree) → Option Work :=
  LoffScaffoldView.View.viewLabel

structure RawSummary (degree : Nat) where
  status : Status
  path : List (Fin degree)
  deriving Repr

namespace RawSummary

def failure {degree : Nat} : RawSummary degree := ⟨.failure, []⟩
def zero {degree : Nat} : RawSummary degree := ⟨.zero, []⟩
def past {degree : Nat} (path : List (Fin degree)) : RawSummary degree := ⟨.past, path⟩
def base {degree : Nat} (path : List (Fin degree)) : RawSummary degree := ⟨.base, path⟩

end RawSummary

noncomputable def observedStatus {radius : Nat}
    (view : Scaffolding.Neighborhood
      (Fin (WorkLabelCount grammar)) (Degree grammar) radius)
    (path : List (Fin (Degree grammar)))
    (expression : ParsingExpression Terminal nonterminalCount) : Status :=
  match viewLabel radius view path with
  | none => .failure
  | some encoded =>
      if h : expression ∈ relevantExpressions grammar then
        decodeLabel grammar encoded ⟨expression, h⟩
      else
        .failure

noncomputable def oldTopLabel {radius : Nat}
    (view : Scaffolding.Neighborhood
      (Fin (WorkLabelCount grammar)) (Degree grammar) radius) :
    Option (Fin (WorkLabelCount grammar)) :=
  viewLabel radius view []


noncomputable def continuePast {radius : Nat}
    (view : Scaffolding.Neighborhood
      (Fin (WorkLabelCount grammar)) (Degree grammar) radius)
    (pathPrefix : List (Fin (Degree grammar)))
    (right : ParsingExpression Terminal nonterminalCount) :
    RawSummary (Degree grammar) :=
  match observedStatus grammar view pathPrefix right with
  | .failure => .failure
  | .zero => .past pathPrefix
  | .past => .past (pathPrefix ++ [directionOf grammar right])
  | .base => .base (pathPrefix ++ [directionOf grammar right])

noncomputable def continueBase
    (pathPrefix : List (Fin (Degree grammar)))
    (right : ParsingExpression Terminal nonterminalCount) :
    RawSummary (Degree grammar) :=
  match Semantic.status grammar total right [] with
  | .failure => .failure
  | _ => .base pathPrefix

noncomputable def approximate {radius : Nat}
    (symbol : Terminal)
    (view : Scaffolding.Neighborhood
      (Fin (WorkLabelCount grammar)) (Degree grammar) radius) :
    Nat → ParsingExpression Terminal nonterminalCount →
      RawSummary (Degree grammar)
  | 0, _ => .failure
  | fuel + 1, expression =>
      match expression with
      | .empty => .zero
      | .failure => .failure
      | .terminal wanted =>
          if wanted = symbol then
            match oldTopLabel grammar view with
            | none => .base []
            | some _ => .past []
          else
            .failure
      | .nonterminal name =>
          approximate symbol view fuel (grammar.rule name)
      | .sequence left right =>
          let leftSummary := approximate symbol view fuel left
          match leftSummary.status with
          | .failure => .failure
          | .zero => approximate symbol view fuel right
          | .past => continuePast grammar view leftSummary.path right
          | .base => continueBase grammar total leftSummary.path right
      | .orderedChoice left right =>
          let leftSummary := approximate symbol view fuel left
          match leftSummary.status with
          | .failure => approximate symbol view fuel right
          | _ => leftSummary
      | .notPredicate body =>
          let bodySummary := approximate symbol view fuel body
          match bodySummary.status with
          | .failure => .zero
          | _ => .failure
      | .andPredicate body =>
          let bodySummary := approximate symbol view fuel body
          match bodySummary.status with
          | .failure => .failure
          | _ => .zero

noncomputable def summaryTarget
    (summary : RawSummary (Degree grammar)) :
    Scaffolding.LocalTarget (Degree grammar) (Radius grammar) :=
  match summary.status with
  | .failure => .missing
  | .zero => .self
  | .past | .base =>
      if h : summary.path.length ≤ Radius grammar then
        .path summary.path h
      else
        .missing

noncomputable def coordinateAt (edge : Fin (Degree grammar)) :
    Option (Coordinate grammar) :=
  if h : edge.val < Fintype.card (Coordinate grammar) then
    some ((coordinateEquiv grammar).symm ⟨edge.val, h⟩)
  else
    none

@[simp] theorem coordinateAt_direction (coordinate : Coordinate grammar) :
    coordinateAt grammar (direction grammar coordinate) = some coordinate := by
  unfold coordinateAt
  rw [dif_pos]
  · congr
    exact (coordinateEquiv grammar).symm_apply_apply coordinate

noncomputable def semanticWorkLabel (input : List Terminal) : WorkLabel grammar :=
  fun coordinate => Semantic.status grammar total coordinate.1 input

noncomputable def idealNode (input : List Terminal) :
    Scaffolding.Node (Fin (WorkLabelCount grammar)) (Degree grammar) :=
  if input = [] then
    { label := none
      edgeOffset := fun _ => none }
  else
    { label := some (encodeLabel grammar (semanticWorkLabel grammar total input))
      edgeOffset := fun edge =>
        match coordinateAt grammar edge with
        | none => none
        | some coordinate =>
            match Semantic.result grammar total coordinate.1 input with
            | .failure => none
            | .success remaining => some (input.length - remaining.length) }

noncomputable def idealScaffold :
    List Terminal → Scaffolding.Scaffold
      (Fin (WorkLabelCount grammar)) (Degree grammar)
  | [] => Scaffolding.Automaton.initialScaffold
  | symbol :: rest =>
      { top := idealNode grammar total (symbol :: rest)
        older := (idealScaffold rest).nodes }

@[simp] theorem idealScaffold_nil :
    idealScaffold grammar total [] = Scaffolding.Automaton.initialScaffold :=
  rfl

@[simp] theorem idealScaffold_nodes_cons (symbol : Terminal) (rest : List Terminal) :
    (idealScaffold grammar total (symbol :: rest)).nodes =
      idealNode grammar total (symbol :: rest) ::
        (idealScaffold grammar total rest).nodes :=
  rfl

@[simp] theorem idealScaffold_nodes_length (input : List Terminal) :
    (idealScaffold grammar total input).nodes.length = input.length + 1 := by
  induction input with
  | nil => rfl
  | cons symbol rest ih => simp [ih]

theorem idealScaffold_nodes_getElem? (input : List Terminal) (position : Nat) :
    (idealScaffold grammar total input).nodes[position]? =
      if position ≤ input.length then
        some (idealNode grammar total (input.drop position))
      else
        none := by
  induction input generalizing position with
  | nil =>
      cases position <;>
        simp [idealScaffold, Scaffolding.Automaton.initialScaffold,
          Scaffolding.Scaffold.nodes, idealNode]
  | cons symbol rest ih =>
      cases position with
      | zero => simp [idealScaffold, Scaffolding.Scaffold.nodes]
      | succ position =>
          simpa [idealScaffold, Scaffolding.Scaffold.nodes] using ih position

theorem drop_length_sub_eq_of_isSuffix {remaining input : List Terminal}
    (suffix : remaining <:+ input) :
    input.drop (input.length - remaining.length) = remaining := by
  rcases suffix with ⟨head, rfl⟩
  simp

theorem follow_idealScaffold_single
    {input remaining : List Terminal} (inputNonempty : input ≠ [])
    (coordinate : Coordinate grammar)
    (resultSuccess :
      Semantic.result grammar total coordinate.1 input = .success remaining) :
    Scaffolding.Scaffold.follow (idealScaffold grammar total input).nodes 0
        [direction grammar coordinate] =
      some (input.length - remaining.length) := by
  cases input with
  | nil => contradiction
  | cons symbol rest =>
      have offsetLe :
          (symbol :: rest).length - remaining.length ≤ (symbol :: rest).length :=
        Nat.sub_le _ _
      rw [Scaffolding.Scaffold.follow]
      simp only [idealScaffold_nodes_cons, List.getElem?_cons_zero]
      have edgeOffset_eq :
        (idealNode grammar total (symbol :: rest)).edgeOffset
            (direction grammar coordinate) =
          some ((symbol :: rest).length - remaining.length) := by
        simp [idealNode, resultSuccess]
      simp [edgeOffset_eq, Scaffolding.Scaffold.follow,
        idealScaffold_nodes_getElem?, offsetLe]

structure SummaryCorrect
    (rest input : List Terminal) (fuel : Nat)
    (expression : ParsingExpression Terminal nonterminalCount)
    (summary : RawSummary (Degree grammar)) : Prop where
  status_eq :
    summary.status = Semantic.status grammar total expression input
  path_length_le : summary.path.length ≤ fuel
  endpoint :
    ∀ {remaining : List Terminal},
      Semantic.result grammar total expression input = .success remaining →
      remaining ≠ input →
      Scaffolding.Scaffold.follow (idealScaffold grammar total rest).nodes 0
          summary.path =
        some (rest.length - remaining.length)
theorem strict_suffix_of_cons_suffix {remaining rest : List Terminal}
    {symbol : Terminal} (suffix : remaining <:+ symbol :: rest)
    (strict : remaining ≠ symbol :: rest) :
    remaining <:+ rest := by
  rcases suffix with ⟨headPart, hhead⟩
  cases headPart with
  | nil =>
      simp only [List.nil_append] at hhead
      exact False.elim (strict hhead)
  | cons head tail =>
      simp only [List.cons_append, List.cons.injEq] at hhead
      exact ⟨tail, hhead.2⟩

theorem follow_append {Work : Type} {degree : Nat}
    (nodes : List (Scaffolding.Node Work degree)) (position : Nat)
    (first second : List (Fin degree)) :
    Scaffolding.Scaffold.follow nodes position (first ++ second) =
      (Scaffolding.Scaffold.follow nodes position first).bind
        (fun middle => Scaffolding.Scaffold.follow nodes middle second) := by
  induction first generalizing position with
  | nil =>
      cases hnode : nodes[position]? with
      | none => cases second <;>
          simp [Scaffolding.Scaffold.follow, hnode]
      | some node => simp [Scaffolding.Scaffold.follow, hnode]
  | cons edge edges ih =>
      cases hnode : nodes[position]? with
      | none => simp [Scaffolding.Scaffold.follow, hnode]
      | some node =>
          cases hedge : node.edgeOffset edge with
          | none => simp [Scaffolding.Scaffold.follow, hnode, hedge]
          | some offset =>
              simp [Scaffolding.Scaffold.follow, hnode, hedge, ih]

@[simp] theorem directionOf_of_mem
    (expression : ParsingExpression Terminal nonterminalCount)
    (relevant : expression ∈ relevantExpressions grammar) :
    directionOf grammar expression = direction grammar ⟨expression, relevant⟩ := by
  simp [directionOf, relevant]

theorem oldTopLabel_idealScaffold (rest : List Terminal) (radius : Nat) :
    oldTopLabel grammar
        ((idealScaffold grammar total rest).topNeighborhood radius) =
      if rest = [] then none
      else some (encodeLabel grammar (semanticWorkLabel grammar total rest)) := by
  cases rest with
  | nil => cases radius <;> rfl
  | cons symbol rest =>
      cases radius <;>
        simp [oldTopLabel, viewLabel,
          LoffScaffoldView.View.viewLabel, idealScaffold,
          Scaffolding.Scaffold.topNeighborhood, idealNode]

theorem observedStatus_idealScaffold
    {rest remaining : List Terminal} {radius : Nat}
    (path : List (Fin (Degree grammar)))
    (expression : ParsingExpression Terminal nonterminalCount)
    (relevant : expression ∈ relevantExpressions grammar)
    (pathFits : path.length ≤ radius)
    (pathEndpoint :
      Scaffolding.Scaffold.follow (idealScaffold grammar total rest).nodes 0 path =
        some (rest.length - remaining.length))
    (remainingSuffix : remaining <:+ rest)
    (remainingNonempty : remaining ≠ []) :
    observedStatus grammar
        ((idealScaffold grammar total rest).topNeighborhood radius)
        path expression =
      Semantic.status grammar total expression remaining := by
  let coordinate : Coordinate grammar := ⟨expression, relevant⟩
  have viewEq :=
    LoffScaffoldView.View.viewLabel_topNeighborhood_eq_follow
      (idealScaffold grammar total rest) path pathFits
  rw [pathEndpoint] at viewEq
  have offsetLe : rest.length - remaining.length ≤ rest.length := Nat.sub_le _ _
  have dropEq := drop_length_sub_eq_of_isSuffix remainingSuffix
  have labelEq :
      LoffScaffoldView.View.labelAt (idealScaffold grammar total rest).nodes
          (rest.length - remaining.length) =
        some (encodeLabel grammar (semanticWorkLabel grammar total remaining)) := by
    rw [LoffScaffoldView.View.labelAt, idealScaffold_nodes_getElem?]
    rw [if_pos offsetLe]
    simp only [dropEq]
    simp [idealNode, remainingNonempty]
  simp [labelEq] at viewEq
  simpa [observedStatus, viewEq, relevant, semanticWorkLabel, coordinate] using
    (show decodeLabel grammar
        (encodeLabel grammar (semanticWorkLabel grammar total remaining))
        ⟨expression, relevant⟩ =
      Semantic.status grammar total expression remaining by simp [semanticWorkLabel])

theorem follow_idealScaffold_append_direction
    {outer middle remaining : List Terminal}
    (path : List (Fin (Degree grammar)))
    (coordinate : Coordinate grammar)
    (pathEndpoint :
      Scaffolding.Scaffold.follow (idealScaffold grammar total outer).nodes 0 path =
        some (outer.length - middle.length))
    (middleSuffix : middle <:+ outer)
    (middleNonempty : middle ≠ [])
    (resultSuccess :
      Semantic.result grammar total coordinate.1 middle = .success remaining) :
    Scaffolding.Scaffold.follow (idealScaffold grammar total outer).nodes 0
        (path ++ [direction grammar coordinate]) =
      some (outer.length - remaining.length) := by
  have remainingSuffix :=
    Semantic.result_success_isSuffix grammar total resultSuccess
  have middleLe := middleSuffix.length_le
  have remainingLe := remainingSuffix.length_le
  have positionEq :
      (outer.length - middle.length) + (middle.length - remaining.length) =
        outer.length - remaining.length := by
    omega
  rw [follow_append, pathEndpoint, Option.bind_some]
  have nodeEq :
      (idealScaffold grammar total outer).nodes[outer.length - middle.length]? =
        some (idealNode grammar total middle) := by
    rw [idealScaffold_nodes_getElem?]
    simp [drop_length_sub_eq_of_isSuffix middleSuffix]
  have edgeEq :
      (idealNode grammar total middle).edgeOffset
          (direction grammar coordinate) =
        some (middle.length - remaining.length) := by
    simp [idealNode, middleNonempty, resultSuccess]
  rw [Scaffolding.Scaffold.follow, nodeEq]
  simp [edgeEq, Scaffolding.Scaffold.follow, positionEq,
    idealScaffold_nodes_getElem?]

set_option autoImplicit false in
theorem approximate_correct
    {radius fuel : Nat} {symbol : Terminal} {rest : List Terminal}
    (fuelFits : fuel ≤ radius)
    (expression : ParsingExpression Terminal nonterminalCount)
    (relevant : expression ∈ relevantExpressions grammar)
    (bounded : CallBound
      (fun child parent : Coordinate grammar =>
        SameInputCall grammar total (symbol :: rest) child.1 parent.1)
      fuel ⟨expression, relevant⟩) :
    SummaryCorrect grammar total rest (symbol :: rest) fuel expression
      (approximate grammar total symbol
        ((idealScaffold grammar total rest).topNeighborhood radius)
        fuel expression) := by
  induction fuel generalizing expression with
  | zero => simp [CallBound] at bounded
  | succ fuel ih =>
      rw [CallBound] at bounded
      cases expression with
      | empty =>
          refine ⟨?_, by simp [approximate, RawSummary.zero], ?_⟩
          · simp [approximate, RawSummary.zero, Semantic.status]
          · intro remaining hresult hstrict
            simp at hresult
            exact False.elim (hstrict hresult.symm)
      | failure =>
          refine ⟨?_, by simp [approximate, RawSummary.failure], ?_⟩
          · simp [approximate, RawSummary.failure, Semantic.status]
          · intro remaining hresult
            simp at hresult
      | terminal wanted =>
          by_cases hwanted : wanted = symbol
          · subst wanted
            simp only [approximate]
            rw [oldTopLabel_idealScaffold]
            by_cases hrest : rest = []
            · subst rest
              refine ⟨?_, by simp [RawSummary.base], ?_⟩
              · simp [RawSummary.base, Semantic.status,
                  PegGrammar.terminalResult]
              · intro remaining hresult hstrict
                simp [PegGrammar.terminalResult] at hresult
                subst remaining
                simp [RawSummary.base,
                  Scaffolding.Scaffold.follow,
                  idealScaffold, Scaffolding.Automaton.initialScaffold,
                  Scaffolding.Scaffold.nodes]
            · refine ⟨?_, by simp [RawSummary.past, hrest], ?_⟩
              · simp [RawSummary.past, Semantic.status,
                  PegGrammar.terminalResult, hrest]
              · intro remaining hresult hstrict
                simp [PegGrammar.terminalResult] at hresult
                subst remaining
                simp [RawSummary.past, hrest,
                  Scaffolding.Scaffold.follow,
                  Scaffolding.Scaffold.nodes]
          · have hactual : symbol ≠ wanted := Ne.symm hwanted
            refine ⟨?_, by simp [approximate, RawSummary.failure, hwanted], ?_⟩
            · simp [approximate, RawSummary.failure, Semantic.status,
                PegGrammar.terminalResult, hwanted, hactual]
            · intro remaining hresult
              simp [PegGrammar.terminalResult, hactual] at hresult
      | nonterminal name =>
          have bodyRelevant := rule_mem_relevantExpressions grammar name
          have bodyBound := bounded ⟨grammar.rule name, bodyRelevant⟩
            (by exact SameInputCall.nonterminal name)
          have correct := ih (Nat.le_of_succ_le fuelFits)
            (grammar.rule name) bodyRelevant bodyBound
          refine ⟨?_, ?_, ?_⟩
          · simpa [approximate, Semantic.status] using correct.status_eq
          · simpa [approximate] using
              correct.path_length_le.trans (Nat.le_succ fuel)
          · intro remaining hresult hstrict
            apply correct.endpoint (remaining := remaining)
            · simpa using hresult
            · exact hstrict
      | sequence left right =>
          have leftRelevant : left ∈ relevantExpressions grammar :=
            subexpression_mem_relevantExpressions
              (parent := .sequence left right) grammar relevant
              (by simp [subexpressions])
          have rightRelevant : right ∈ relevantExpressions grammar :=
            subexpression_mem_relevantExpressions
              (parent := .sequence left right) grammar relevant
              (by simp [subexpressions])
          have leftBound := bounded ⟨left, leftRelevant⟩
            (by exact SameInputCall.sequenceLeft left right)
          have leftCorrect := ih (Nat.le_of_succ_le fuelFits)
            left leftRelevant leftBound
          cases leftResult :
              Semantic.result grammar total left (symbol :: rest) with
          | failure =>
              have semanticLeftFailure :
                  Semantic.status grammar total left (symbol :: rest) =
                    .failure :=
                (Semantic.status_eq_failure_iff grammar total _ _).mpr
                  leftResult
              have leftStatus :
                  (approximate grammar total symbol
                    ((idealScaffold grammar total rest).topNeighborhood radius)
                    fuel left).status = .failure :=
                leftCorrect.status_eq.trans semanticLeftFailure
              have sequenceResult :=
                Semantic.result_sequence_of_failure (right := right)
                  grammar total leftResult
              have sequenceStatus :=
                (Semantic.status_eq_failure_iff grammar total _ _).mpr
                  sequenceResult
              refine ⟨?_, by simp [approximate, leftStatus,
                RawSummary.failure], ?_⟩
              · simp [approximate, leftStatus, RawSummary.failure,
                  sequenceStatus]
              · intro remaining result
                rw [sequenceResult] at result
                contradiction
          | success middle =>
              have sequenceResult :=
                Semantic.result_sequence_of_success (right := right)
                  grammar total leftResult
              by_cases middleSame : middle = symbol :: rest
              · subst middle
                have semanticLeftZero :
                    Semantic.status grammar total left (symbol :: rest) =
                      .zero :=
                  (Semantic.status_eq_zero_iff grammar total _ _).mpr
                    leftResult
                have leftStatus :
                    (approximate grammar total symbol
                      ((idealScaffold grammar total rest).topNeighborhood radius)
                      fuel left).status = .zero :=
                  leftCorrect.status_eq.trans semanticLeftZero
                have rightBound := bounded ⟨right, rightRelevant⟩
                  (by
                    exact SameInputCall.sequenceRight left right
                      semanticLeftZero)
                have rightCorrect := ih (Nat.le_of_succ_le fuelFits)
                  right rightRelevant rightBound
                refine ⟨?_, ?_, ?_⟩
                · simpa [approximate, leftStatus, Semantic.status,
                    sequenceResult] using rightCorrect.status_eq
                · simpa [approximate, leftStatus] using
                    rightCorrect.path_length_le.trans (Nat.le_succ fuel)
                · intro remaining result strict
                  rw [sequenceResult] at result
                  have endpoint := rightCorrect.endpoint result strict
                  simpa [approximate, leftStatus] using endpoint
              · have middleSuffix :=
                  Semantic.result_success_isSuffix grammar total leftResult
                have middleTailSuffix :=
                  strict_suffix_of_cons_suffix middleSuffix middleSame
                have leftEndpoint :=
                  leftCorrect.endpoint leftResult middleSame
                by_cases middleEmpty : middle = []
                · subst middle
                  have semanticLeftBase :
                      Semantic.status grammar total left (symbol :: rest) =
                        .base :=
                    (Semantic.status_eq_base_iff grammar total left
                      (by simp)).mpr leftResult
                  have leftStatus :
                      (approximate grammar total symbol
                        ((idealScaffold grammar total rest).topNeighborhood radius)
                        fuel left).status = .base :=
                    leftCorrect.status_eq.trans semanticLeftBase
                  rcases Semantic.status_on_nil grammar total right with
                    rightFailure | rightZero
                  · have rightResult :=
                      (Semantic.status_eq_failure_iff grammar total right []).mp
                        rightFailure
                    have sequenceFailure :
                        Semantic.result grammar total (.sequence left right)
                            (symbol :: rest) = .failure :=
                      sequenceResult.trans rightResult
                    have sequenceFailureStatus :=
                      (Semantic.status_eq_failure_iff grammar total _ _).mpr
                        sequenceFailure
                    refine ⟨?_, by simp [approximate, leftStatus,
                      continueBase, rightFailure, RawSummary.failure], ?_⟩
                    · simp [approximate, leftStatus, continueBase,
                        rightFailure, RawSummary.failure,
                        sequenceFailureStatus]
                    · intro remaining result
                      rw [sequenceFailure] at result
                      contradiction
                  · have rightResult :=
                      (Semantic.status_eq_zero_iff grammar total right []).mp
                        rightZero
                    have sequenceSuccess :
                        Semantic.result grammar total (.sequence left right)
                            (symbol :: rest) = .success [] :=
                      sequenceResult.trans rightResult
                    have sequenceBaseStatus :=
                      (Semantic.status_eq_base_iff grammar total
                        (.sequence left right) (by simp)).mpr sequenceSuccess
                    refine ⟨?_, ?_, ?_⟩
                    · simp [approximate, leftStatus, continueBase,
                        rightZero, RawSummary.base, sequenceBaseStatus]
                    · simpa [approximate, leftStatus, continueBase,
                        rightZero, RawSummary.base] using
                        leftCorrect.path_length_le.trans (Nat.le_succ fuel)
                    · intro remaining result strict
                      have same : ([] : List Terminal) = remaining :=
                        ParseResult.success.inj
                          (sequenceSuccess.symm.trans result)
                      subst remaining
                      simpa [approximate, leftStatus, continueBase,
                        rightZero, RawSummary.base] using leftEndpoint
                · have semanticLeftPast :
                      Semantic.status grammar total left (symbol :: rest) =
                        .past :=
                    (Semantic.status_eq_past_iff grammar total left _).mpr
                      ⟨middle, leftResult, middleSame, middleEmpty⟩
                  have leftStatus :
                      (approximate grammar total symbol
                        ((idealScaffold grammar total rest).topNeighborhood radius)
                        fuel left).status = .past :=
                    leftCorrect.status_eq.trans semanticLeftPast
                  have leftPathFits :
                      (approximate grammar total symbol
                        ((idealScaffold grammar total rest).topNeighborhood radius)
                        fuel left).path.length ≤ radius :=
                    leftCorrect.path_length_le.trans
                      (Nat.le_of_succ_le fuelFits)
                  have observedRight :=
                    observedStatus_idealScaffold grammar total
                      (approximate grammar total symbol
                        ((idealScaffold grammar total rest).topNeighborhood radius)
                        fuel left).path
                      right rightRelevant leftPathFits leftEndpoint
                      middleTailSuffix middleEmpty
                  cases rightResult :
                      Semantic.result grammar total right middle with
                  | failure =>
                      have semanticRightFailure :
                          Semantic.status grammar total right middle =
                            .failure :=
                        (Semantic.status_eq_failure_iff grammar total _ _).mpr
                          rightResult
                      have observedFailure :=
                        observedRight.trans semanticRightFailure
                      have sequenceFailure :
                          Semantic.result grammar total (.sequence left right)
                              (symbol :: rest) = .failure :=
                        sequenceResult.trans rightResult
                      have sequenceFailureStatus :=
                        (Semantic.status_eq_failure_iff grammar total _ _).mpr
                          sequenceFailure
                      refine ⟨?_, by simp [approximate, leftStatus,
                        continuePast, observedFailure,
                        RawSummary.failure], ?_⟩
                      · simp [approximate, leftStatus, continuePast,
                          observedFailure, RawSummary.failure,
                          sequenceFailureStatus]
                      · intro remaining result
                        rw [sequenceFailure] at result
                        contradiction
                  | success remaining =>
                      have sequenceSuccess :
                          Semantic.result grammar total (.sequence left right)
                              (symbol :: rest) = .success remaining :=
                        sequenceResult.trans rightResult
                      by_cases remainingSame : remaining = middle
                      · subst remaining
                        have semanticRightZero :
                            Semantic.status grammar total right middle =
                              .zero :=
                          (Semantic.status_eq_zero_iff grammar total _ _).mpr
                            rightResult
                        have observedZero :=
                          observedRight.trans semanticRightZero
                        have sequencePastStatus :
                            Semantic.status grammar total
                                (.sequence left right) (symbol :: rest) =
                              .past :=
                          (Semantic.status_eq_past_iff grammar total _ _).mpr
                            ⟨middle, sequenceSuccess, middleSame, middleEmpty⟩
                        refine ⟨?_, ?_, ?_⟩
                        · simp [approximate, leftStatus, continuePast,
                            observedZero, RawSummary.past,
                            sequencePastStatus]
                        · simpa [approximate, leftStatus, continuePast,
                            observedZero, RawSummary.past] using
                            leftCorrect.path_length_le.trans
                              (Nat.le_succ fuel)
                        · intro final result strict
                          have same : middle = final :=
                            ParseResult.success.inj
                              (sequenceSuccess.symm.trans result)
                          subst final
                          simpa [approximate, leftStatus, continuePast,
                            observedZero, RawSummary.past] using leftEndpoint
                      · by_cases remainingEmpty : remaining = []
                        · subst remaining
                          have semanticRightBase :
                              Semantic.status grammar total right middle =
                                .base :=
                            (Semantic.status_eq_base_iff grammar total right
                              middleEmpty).mpr rightResult
                          have observedBase :=
                            observedRight.trans semanticRightBase
                          have sequenceBaseStatus :
                              Semantic.status grammar total
                                  (.sequence left right) (symbol :: rest) =
                                .base :=
                            (Semantic.status_eq_base_iff grammar total
                              (.sequence left right) (by simp)).mpr
                                sequenceSuccess
                          refine ⟨?_, ?_, ?_⟩
                          · simp [approximate, leftStatus, continuePast,
                              observedBase, RawSummary.base,
                              sequenceBaseStatus]
                          · simpa [approximate, leftStatus, continuePast,
                              observedBase, RawSummary.base] using
                              Nat.add_le_add_right
                                leftCorrect.path_length_le 1
                          · intro final result strict
                            have same : ([] : List Terminal) = final :=
                              ParseResult.success.inj
                                (sequenceSuccess.symm.trans result)
                            subst final
                            have appended :=
                              follow_idealScaffold_append_direction grammar total
                                (approximate grammar total symbol
                                  ((idealScaffold grammar total rest).topNeighborhood
                                    radius)
                                  fuel left).path
                                ⟨right, rightRelevant⟩ leftEndpoint
                                middleTailSuffix middleEmpty rightResult
                            simpa [approximate, leftStatus, continuePast,
                              observedBase, RawSummary.base,
                              directionOf_of_mem grammar right rightRelevant] using
                                appended
                        · have remainingSuffix :=
                            Semantic.result_success_isSuffix grammar total
                              rightResult
                          have remainingStrictInput :
                              remaining ≠ symbol :: rest := by
                            intro sameInput
                            subst remaining
                            have inputEqMiddle :
                                symbol :: rest = middle :=
                              remainingSuffix.eq_of_length_le
                                middleSuffix.length_le
                            exact middleSame inputEqMiddle.symm
                          have semanticRightPast :
                              Semantic.status grammar total right middle =
                                .past :=
                            (Semantic.status_eq_past_iff grammar total _ _).mpr
                              ⟨remaining, rightResult, remainingSame,
                                remainingEmpty⟩
                          have observedPast :=
                            observedRight.trans semanticRightPast
                          have sequencePastStatus :
                              Semantic.status grammar total
                                  (.sequence left right) (symbol :: rest) =
                                .past :=
                            (Semantic.status_eq_past_iff grammar total _ _).mpr
                              ⟨remaining, sequenceSuccess,
                                remainingStrictInput, remainingEmpty⟩
                          refine ⟨?_, ?_, ?_⟩
                          · simp [approximate, leftStatus, continuePast,
                              observedPast, RawSummary.past,
                              sequencePastStatus]
                          · simpa [approximate, leftStatus, continuePast,
                              observedPast, RawSummary.past] using
                              Nat.add_le_add_right
                                leftCorrect.path_length_le 1
                          · intro final result strict
                            have same : remaining = final :=
                              ParseResult.success.inj
                                (sequenceSuccess.symm.trans result)
                            subst final
                            have appended :=
                              follow_idealScaffold_append_direction grammar total
                                (approximate grammar total symbol
                                  ((idealScaffold grammar total rest).topNeighborhood
                                    radius)
                                  fuel left).path
                                ⟨right, rightRelevant⟩ leftEndpoint
                                middleTailSuffix middleEmpty rightResult
                            simpa [approximate, leftStatus, continuePast,
                              observedPast, RawSummary.past,
                              directionOf_of_mem grammar right rightRelevant] using
                                appended
      | orderedChoice left right =>
          have leftRelevant : left ∈ relevantExpressions grammar :=
            subexpression_mem_relevantExpressions
              (parent := .orderedChoice left right) grammar relevant
              (by simp [subexpressions])
          have rightRelevant : right ∈ relevantExpressions grammar :=
            subexpression_mem_relevantExpressions
              (parent := .orderedChoice left right) grammar relevant
              (by simp [subexpressions])
          have leftBound := bounded ⟨left, leftRelevant⟩
            (by exact SameInputCall.choiceLeft left right)
          have leftCorrect := ih (Nat.le_of_succ_le fuelFits)
            left leftRelevant leftBound
          cases leftResult :
              Semantic.result grammar total left (symbol :: rest) with
          | failure =>
              have semanticLeftFailure :
                  Semantic.status grammar total left (symbol :: rest) =
                    .failure :=
                (Semantic.status_eq_failure_iff grammar total _ _).mpr
                  leftResult
              have leftStatus :
                  (approximate grammar total symbol
                    ((idealScaffold grammar total rest).topNeighborhood radius)
                    fuel left).status = .failure :=
                leftCorrect.status_eq.trans semanticLeftFailure
              have rightBound := bounded ⟨right, rightRelevant⟩
                (by
                  exact SameInputCall.choiceRight left right
                    semanticLeftFailure)
              have rightCorrect := ih (Nat.le_of_succ_le fuelFits)
                right rightRelevant rightBound
              have choiceResult :=
                Semantic.result_choice_of_failure (right := right)
                  grammar total leftResult
              refine ⟨?_, ?_, ?_⟩
              · simpa [approximate, leftStatus, Semantic.status,
                  choiceResult] using rightCorrect.status_eq
              · simpa [approximate, leftStatus] using
                  rightCorrect.path_length_le.trans (Nat.le_succ fuel)
              · intro remaining result strict
                rw [choiceResult] at result
                have endpoint := rightCorrect.endpoint result strict
                simpa [approximate, leftStatus] using endpoint
          | success middle =>
              have choiceResult :=
                Semantic.result_choice_of_success (right := right)
                  grammar total leftResult
              have leftNotFailure :
                  (approximate grammar total symbol
                    ((idealScaffold grammar total rest).topNeighborhood radius)
                    fuel left).status ≠ .failure := by
                intro summaryFailure
                have semanticFailure :
                    Semantic.status grammar total left (symbol :: rest) =
                      .failure :=
                  leftCorrect.status_eq.symm.trans summaryFailure
                have resultFailure :=
                  (Semantic.status_eq_failure_iff grammar total _ _).mp
                    semanticFailure
                rw [leftResult] at resultFailure
                contradiction
              cases leftStatus :
                  (approximate grammar total symbol
                    ((idealScaffold grammar total rest).topNeighborhood radius)
                    fuel left).status with
              | failure => exact False.elim (leftNotFailure leftStatus)
              | zero =>
                  refine ⟨?_, ?_, ?_⟩
                  · simpa [approximate, leftStatus, Semantic.status,
                      choiceResult, leftResult] using leftCorrect.status_eq
                  · simpa [approximate, leftStatus] using
                      leftCorrect.path_length_le.trans (Nat.le_succ fuel)
                  · intro remaining result strict
                    have same : middle = remaining :=
                      ParseResult.success.inj (choiceResult.symm.trans result)
                    subst remaining
                    simpa [approximate, leftStatus] using
                      leftCorrect.endpoint leftResult strict
              | past =>
                  refine ⟨?_, ?_, ?_⟩
                  · simpa [approximate, leftStatus, Semantic.status,
                      choiceResult, leftResult] using leftCorrect.status_eq
                  · simpa [approximate, leftStatus] using
                      leftCorrect.path_length_le.trans (Nat.le_succ fuel)
                  · intro remaining result strict
                    have same : middle = remaining :=
                      ParseResult.success.inj (choiceResult.symm.trans result)
                    subst remaining
                    simpa [approximate, leftStatus] using
                      leftCorrect.endpoint leftResult strict
              | base =>
                  refine ⟨?_, ?_, ?_⟩
                  · simpa [approximate, leftStatus, Semantic.status,
                      choiceResult, leftResult] using leftCorrect.status_eq
                  · simpa [approximate, leftStatus] using
                      leftCorrect.path_length_le.trans (Nat.le_succ fuel)
                  · intro remaining result strict
                    have same : middle = remaining :=
                      ParseResult.success.inj (choiceResult.symm.trans result)
                    subst remaining
                    simpa [approximate, leftStatus] using
                      leftCorrect.endpoint leftResult strict
      | notPredicate body =>
          have bodyRelevant : body ∈ relevantExpressions grammar :=
            subexpression_mem_relevantExpressions
              (parent := .notPredicate body) grammar relevant
              (by simp [subexpressions])
          have bodyBound := bounded ⟨body, bodyRelevant⟩
            (by exact SameInputCall.notBody body)
          have bodyCorrect := ih (Nat.le_of_succ_le fuelFits)
            body bodyRelevant bodyBound
          cases bodyResult :
              Semantic.result grammar total body (symbol :: rest) with
          | failure =>
              have bodyStatus :
                  (approximate grammar total symbol
                    ((idealScaffold grammar total rest).topNeighborhood radius)
                    fuel body).status = .failure :=
                bodyCorrect.status_eq.trans
                  ((Semantic.status_eq_failure_iff grammar total _ _).mpr
                    bodyResult)
              have predicateResult :=
                Semantic.result_not_of_failure grammar total bodyResult
              refine ⟨?_, by simp [approximate, bodyStatus, RawSummary.zero], ?_⟩
              · simp [approximate, bodyStatus, RawSummary.zero,
                  Semantic.status, predicateResult]
              · intro remaining result strict
                have same := ParseResult.success.inj
                  (predicateResult.symm.trans result)
                exact False.elim (strict same.symm)
          | success middle =>
              have bodyNotFailure :
                  (approximate grammar total symbol
                    ((idealScaffold grammar total rest).topNeighborhood radius)
                    fuel body).status ≠ .failure := by
                intro summaryFailure
                have semanticFailure :
                    Semantic.status grammar total body (symbol :: rest) =
                      .failure :=
                  bodyCorrect.status_eq.symm.trans summaryFailure
                have resultFailure :=
                  (Semantic.status_eq_failure_iff grammar total _ _).mp
                    semanticFailure
                rw [bodyResult] at resultFailure
                contradiction
              have predicateResult :=
                Semantic.result_not_of_success grammar total bodyResult
              cases bodyStatus :
                  (approximate grammar total symbol
                    ((idealScaffold grammar total rest).topNeighborhood radius)
                    fuel body).status with
              | failure => exact False.elim (bodyNotFailure bodyStatus)
              | zero =>
                  refine ⟨?_, by simp [approximate, bodyStatus,
                    RawSummary.failure], ?_⟩
                  · simp [approximate, bodyStatus, RawSummary.failure,
                      Semantic.status, predicateResult]
                  · intro remaining result
                    rw [predicateResult] at result
                    contradiction
              | past =>
                  refine ⟨?_, by simp [approximate, bodyStatus,
                    RawSummary.failure], ?_⟩
                  · simp [approximate, bodyStatus, RawSummary.failure,
                      Semantic.status, predicateResult]
                  · intro remaining result
                    rw [predicateResult] at result
                    contradiction
              | base =>
                  refine ⟨?_, by simp [approximate, bodyStatus,
                    RawSummary.failure], ?_⟩
                  · simp [approximate, bodyStatus, RawSummary.failure,
                      Semantic.status, predicateResult]
                  · intro remaining result
                    rw [predicateResult] at result
                    contradiction
      | andPredicate body =>
          have bodyRelevant : body ∈ relevantExpressions grammar :=
            subexpression_mem_relevantExpressions
              (parent := .andPredicate body) grammar relevant
              (by simp [subexpressions])
          have bodyBound := bounded ⟨body, bodyRelevant⟩
            (by exact SameInputCall.andBody body)
          have bodyCorrect := ih (Nat.le_of_succ_le fuelFits)
            body bodyRelevant bodyBound
          cases bodyResult :
              Semantic.result grammar total body (symbol :: rest) with
          | failure =>
              have bodyStatus :
                  (approximate grammar total symbol
                    ((idealScaffold grammar total rest).topNeighborhood radius)
                    fuel body).status = .failure :=
                bodyCorrect.status_eq.trans
                  ((Semantic.status_eq_failure_iff grammar total _ _).mpr
                    bodyResult)
              have predicateResult :=
                Semantic.result_and_of_failure grammar total bodyResult
              refine ⟨?_, by simp [approximate, bodyStatus,
                RawSummary.failure], ?_⟩
              · simp [approximate, bodyStatus, RawSummary.failure,
                  Semantic.status, predicateResult]
              · intro remaining result
                rw [predicateResult] at result
                contradiction
          | success middle =>
              have bodyNotFailure :
                  (approximate grammar total symbol
                    ((idealScaffold grammar total rest).topNeighborhood radius)
                    fuel body).status ≠ .failure := by
                intro summaryFailure
                have semanticFailure :
                    Semantic.status grammar total body (symbol :: rest) =
                      .failure :=
                  bodyCorrect.status_eq.symm.trans summaryFailure
                have resultFailure :=
                  (Semantic.status_eq_failure_iff grammar total _ _).mp
                    semanticFailure
                rw [bodyResult] at resultFailure
                contradiction
              have predicateResult :=
                Semantic.result_and_of_success grammar total bodyResult
              cases bodyStatus :
                  (approximate grammar total symbol
                    ((idealScaffold grammar total rest).topNeighborhood radius)
                    fuel body).status with
              | failure => exact False.elim (bodyNotFailure bodyStatus)
              | zero =>
                  refine ⟨?_, by simp [approximate, bodyStatus,
                    RawSummary.zero], ?_⟩
                  · simp [approximate, bodyStatus, RawSummary.zero,
                      Semantic.status, predicateResult]
                  · intro remaining result strict
                    have same := ParseResult.success.inj
                      (predicateResult.symm.trans result)
                    exact False.elim (strict same.symm)
              | past =>
                  refine ⟨?_, by simp [approximate, bodyStatus,
                    RawSummary.zero], ?_⟩
                  · simp [approximate, bodyStatus, RawSummary.zero,
                      Semantic.status, predicateResult]
                  · intro remaining result strict
                    have same := ParseResult.success.inj
                      (predicateResult.symm.trans result)
                    exact False.elim (strict same.symm)
              | base =>
                  refine ⟨?_, by simp [approximate, bodyStatus,
                    RawSummary.zero], ?_⟩
                  · simp [approximate, bodyStatus, RawSummary.zero,
                      Semantic.status, predicateResult]
                  · intro remaining result strict
                    have same := ParseResult.success.inj
                      (predicateResult.symm.trans result)
                    exact False.elim (strict same.symm)

noncomputable def action
    (symbol : Terminal)
    (view : Scaffolding.Neighborhood
      (Fin (WorkLabelCount grammar)) (Degree grammar) (Radius grammar)) :
    Scaffolding.Action (Fin 2) (Fin (WorkLabelCount grammar))
      (Degree grammar) (Radius grammar) :=
  let summarize := approximate grammar total symbol view (Radius grammar)
  { nextState :=
      if (summarize (.nonterminal grammar.start)).status = .base then 1 else 0
    newLabel := encodeLabel grammar (fun coordinate => (summarize coordinate.1).status)
    target := fun edge =>
      match coordinateAt grammar edge with
      | none => .missing
      | some coordinate => summaryTarget grammar (summarize coordinate.1) }

noncomputable def automaton :
    Scaffolding.Automaton Terminal 2 (WorkLabelCount grammar)
      (Degree grammar) (Radius grammar) where
  degreePositive := by simp [Degree]
  initialState :=
    if Semantic.status grammar total (.nonterminal grammar.start) [] = .zero then 1 else 0
  accepting := {1}
  transition := fun _ symbol view => action grammar total symbol view

theorem recognizes_iff_result (input : List Terminal) :
    grammar.Recognizes input ↔
      Semantic.result grammar total (.nonterminal grammar.start) input = .success [] := by
  constructor
  · intro hrecognizes
    exact Semantic.result_eq_of_evaluates grammar total hrecognizes
  · intro hresult
    change grammar.Evaluates (.nonterminal grammar.start) input (.success [])
    simpa [hresult] using
      Semantic.result_spec grammar total (.nonterminal grammar.start) input

theorem automaton_accepts_nil_iff :
    (automaton grammar total).Accepts [] ↔ grammar.Recognizes [] := by
  rw [recognizes_iff_result grammar total]
  rw [← Semantic.status_eq_zero_iff grammar total (.nonterminal grammar.start) []]
  simp [Scaffolding.Automaton.Accepts, Scaffolding.Automaton.run, automaton]

theorem radius_correct (symbol : Terminal) (rest : List Terminal)
    (expression : ParsingExpression Terminal nonterminalCount)
    (relevant : expression ∈ relevantExpressions grammar) :
    SummaryCorrect grammar total rest (symbol :: rest) (Radius grammar) expression
      (approximate grammar total symbol
        ((idealScaffold grammar total rest).topNeighborhood (Radius grammar))
        (Radius grammar) expression) := by
  exact approximate_correct grammar total (le_refl _) expression relevant
    (callBound_radius grammar total (symbol :: rest) ⟨expression, relevant⟩)

noncomputable def semanticState (input : List Terminal) : Fin 2 := by
  classical
  exact if Semantic.result grammar total (.nonterminal grammar.start) input = .success []
    then 1 else 0

theorem action_nextState (symbol : Terminal) (rest : List Terminal) :
    (action grammar total symbol
      ((idealScaffold grammar total rest).topNeighborhood (Radius grammar))).nextState =
      semanticState grammar total (symbol :: rest) := by
  classical
  have correct := radius_correct grammar total symbol rest
    (.nonterminal grammar.start)
    (nonterminal_mem_relevantExpressions grammar grammar.start)
  have statusEq := correct.status_eq
  have baseIff := Semantic.status_eq_base_iff grammar total
    (.nonterminal grammar.start) (show symbol :: rest ≠ [] by simp)
  simp [action, semanticState, statusEq, baseIff]

theorem action_newLabel (symbol : Terminal) (rest : List Terminal) :
    (action grammar total symbol
      ((idealScaffold grammar total rest).topNeighborhood (Radius grammar))).newLabel =
      encodeLabel grammar (semanticWorkLabel grammar total (symbol :: rest)) := by
  change encodeLabel grammar (fun coordinate =>
    (approximate grammar total symbol
      ((idealScaffold grammar total rest).topNeighborhood (Radius grammar))
      (Radius grammar) coordinate.1).status) = _
  congr 1
  funext coordinate
  exact (radius_correct grammar total symbol rest coordinate.1
    coordinate.property).status_eq

theorem extend_edgeOffset (symbol : Terminal) (rest : List Terminal)
    (edge : Fin (Degree grammar)) :
    (Scaffolding.Automaton.extendScaffold (idealScaffold grammar total rest)
      (action grammar total symbol
        ((idealScaffold grammar total rest).topNeighborhood (Radius grammar)))).top.edgeOffset edge =
      (idealNode grammar total (symbol :: rest)).edgeOffset edge := by
  classical
  simp only [Scaffolding.Automaton.extendScaffold]
  cases coordinateEq : coordinateAt grammar edge with
  | none => simp [action, coordinateEq, idealNode]
  | some coordinate =>
      simp only [action, coordinateEq]
      simp only [idealNode, List.cons_ne_nil, if_false, coordinateEq]
      let summary := approximate grammar total symbol
        ((idealScaffold grammar total rest).topNeighborhood (Radius grammar))
        (Radius grammar) coordinate.1
      have correct := radius_correct grammar total symbol rest
        coordinate.1 coordinate.property
      cases resultEq :
          Semantic.result grammar total coordinate.1 (symbol :: rest) with
      | failure =>
          have semanticFailure :
              Semantic.status grammar total coordinate.1 (symbol :: rest) =
                .failure :=
            (Semantic.status_eq_failure_iff grammar total _ _).mpr resultEq
          have summaryFailure : summary.status = .failure :=
            correct.status_eq.trans semanticFailure
          simp [summaryTarget, summary, summaryFailure]
      | success remaining =>
          by_cases remainingSame : remaining = symbol :: rest
          · subst remaining
            have semanticZero :
                Semantic.status grammar total coordinate.1 (symbol :: rest) =
                  .zero :=
              (Semantic.status_eq_zero_iff grammar total _ _).mpr resultEq
            have summaryZero : summary.status = .zero :=
              correct.status_eq.trans semanticZero
            simp [summaryTarget, summary, summaryZero]
          · have endpoint := correct.endpoint resultEq remainingSame
            have remainingSuffix :=
              Semantic.result_success_isSuffix grammar total resultEq
            have tailSuffix :=
              strict_suffix_of_cons_suffix remainingSuffix remainingSame
            have remainingLe := tailSuffix.length_le
            have offsetEq :
                (rest.length - remaining.length) + 1 =
                  (symbol :: rest).length - remaining.length := by
              simp only [List.length_cons]
              omega
            by_cases remainingEmpty : remaining = []
            · subst remaining
              have semanticBase :
                  Semantic.status grammar total coordinate.1 (symbol :: rest) =
                    .base :=
                (Semantic.status_eq_base_iff grammar total _ (by simp)).mpr
                  resultEq
              have summaryBase : summary.status = .base :=
                correct.status_eq.trans semanticBase
              simp [summaryTarget, summary, summaryBase,
                correct.path_length_le, endpoint]
            · have semanticPast :
                  Semantic.status grammar total coordinate.1 (symbol :: rest) =
                    .past :=
                (Semantic.status_eq_past_iff grammar total _ _).mpr
                  ⟨remaining, resultEq, remainingSame, remainingEmpty⟩
              have summaryPast : summary.status = .past :=
                correct.status_eq.trans semanticPast
              simp [summaryTarget, summary, summaryPast,
                correct.path_length_le, endpoint, offsetEq]

theorem extend_idealScaffold (symbol : Terminal) (rest : List Terminal) :
    Scaffolding.Automaton.extendScaffold (idealScaffold grammar total rest)
      (action grammar total symbol
        ((idealScaffold grammar total rest).topNeighborhood (Radius grammar))) =
      idealScaffold grammar total (symbol :: rest) := by
  simp only [Scaffolding.Automaton.extendScaffold, idealScaffold,
    Scaffolding.Scaffold.mk.injEq, idealNode, List.cons_ne_nil, if_false,
    Scaffolding.Node.mk.injEq]
  refine ⟨⟨?_, ?_⟩, trivial⟩
  · exact congrArg some (action_newLabel grammar total symbol rest)
  · funext edge
    exact extend_edgeOffset grammar total symbol rest edge

theorem semanticState_nil :
    semanticState grammar total [] = (automaton grammar total).initialState := by
  classical
  have zeroIff := Semantic.status_eq_zero_iff grammar total
    (.nonterminal grammar.start) []
  simp [semanticState, automaton, zeroIff]

theorem step_idealScaffold (state : Fin 2) (symbol : Terminal)
    (rest : List Terminal) :
    (automaton grammar total).step
        (state, idealScaffold grammar total rest) symbol =
      (semanticState grammar total (symbol :: rest),
        idealScaffold grammar total (symbol :: rest)) := by
  change
    ((action grammar total symbol
      ((idealScaffold grammar total rest).topNeighborhood (Radius grammar))).nextState,
      Scaffolding.Automaton.extendScaffold (idealScaffold grammar total rest)
        (action grammar total symbol
          ((idealScaffold grammar total rest).topNeighborhood (Radius grammar)))) = _
  rw [action_nextState grammar total, extend_idealScaffold grammar total]

theorem foldl_step_idealScaffold (scannedReverse remaining : List Terminal) :
    remaining.foldl (automaton grammar total).step
        (semanticState grammar total scannedReverse,
          idealScaffold grammar total scannedReverse) =
      (semanticState grammar total (remaining.reverse ++ scannedReverse),
        idealScaffold grammar total (remaining.reverse ++ scannedReverse)) := by
  induction remaining generalizing scannedReverse with
  | nil => simp
  | cons symbol remaining ih =>
      simp only [List.foldl_cons]
      rw [step_idealScaffold grammar total]
      rw [ih (symbol :: scannedReverse)]
      simp [List.reverse_cons, List.append_assoc]

theorem run_eq_idealScaffold (input : List Terminal) :
    (automaton grammar total).run input =
      (semanticState grammar total input.reverse,
        idealScaffold grammar total input.reverse) := by
  unfold Scaffolding.Automaton.run
  rw [← semanticState_nil grammar total]
  simpa using
    foldl_step_idealScaffold grammar total ([] : List Terminal) input

theorem automaton_accepts_iff (input : List Terminal) :
    (automaton grammar total).Accepts input ↔
      grammar.Recognizes input.reverse := by
  rw [recognizes_iff_result grammar total]
  unfold Scaffolding.Automaton.Accepts
  rw [run_eq_idealScaffold grammar total]
  classical
  simp [semanticState, automaton]

end Construction

end PegSeparation.External.LoffForwardRepaired
