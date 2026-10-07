import PegSeparation.Common.Loff.Semantics


namespace PegSeparation.SCAToPEG

open PegSeparation
open PegSeparation.Scaffolding


abbrev BoundedPath (degree radius : Nat) :=
  { directions : List (Fin degree) // directions.length ≤ radius }

abbrev BoundedPathVector (degree radius : Nat) :=
  Σ length : Fin (radius + 1), List.Vector (Fin degree) length.val

noncomputable def boundedPathEquiv (degree radius : Nat) :
    BoundedPath degree radius ≃ BoundedPathVector degree radius where
  toFun path :=
    ⟨⟨path.1.length, by omega⟩, ⟨path.1, rfl⟩⟩
  invFun path :=
    ⟨path.2.toList, by
      simpa using Nat.le_of_lt_succ path.1.isLt⟩
  left_inv path := by
    apply Subtype.ext
    rfl
  right_inv path := by
    rcases path with ⟨⟨length, lengthFits⟩, ⟨directions, directionsLength⟩⟩
    simp only [List.Vector.toList] at directionsLength ⊢
    subst length
    rfl

noncomputable instance boundedPathFintype (degree radius : Nat) :
    Fintype (BoundedPath degree radius) :=
  Fintype.ofEquiv (BoundedPathVector degree radius)
    (boundedPathEquiv degree radius).symm

noncomputable instance boundedPathDecidableEq (degree radius : Nat) :
    DecidableEq (BoundedPath degree radius) := Classical.decEq _

def emptyPath (degree radius : Nat) : BoundedPath degree radius :=
  ⟨[], by simp⟩

def boundedPathOfList {degree radius : Nat}
    (directions : List (Fin degree)) (withinRadius : directions.length ≤ radius) :
    BoundedPath degree radius :=
  ⟨directions, withinRadius⟩

@[simp] theorem boundedPathOfList_val {degree radius : Nat}
    (directions : List (Fin degree)) (withinRadius : directions.length ≤ radius) :
    (boundedPathOfList directions withinRadius : BoundedPath degree radius).1 = directions :=
  rfl

def BoundedPath.tail {degree radius : Nat}
    (path : BoundedPath degree radius) : BoundedPath degree radius :=
  ⟨path.1.tail, by
    have tailLe : path.1.tail.length ≤ path.1.length := by
      cases path.1 <;> simp
    exact tailLe.trans path.2⟩

@[simp] theorem emptyPath_val (degree radius : Nat) :
    (emptyPath degree radius).1 = [] := rfl

theorem BoundedPath.tail_lt {degree radius : Nat}
    (path : BoundedPath degree radius) (nonempty : path.1 ≠ []) :
    path.tail.1.length < path.1.length := by
  rcases path with ⟨directions, withinRadius⟩
  cases directions with
  | nil => exact (nonempty rfl).elim
  | cons direction directions => simp [BoundedPath.tail]


@[reducible] noncomputable def neighborhoodFintype
    (WorkLabel : Type) [Fintype WorkLabel]
    (degree : Nat) : (radius : Nat) →
      Fintype (Neighborhood WorkLabel degree radius)
  | 0 => inferInstanceAs (Fintype (Option WorkLabel))
  | radius + 1 => by
      letI := neighborhoodFintype WorkLabel degree radius
      exact inferInstanceAs
        (Fintype (Option WorkLabel ×
          (Fin degree → Option (Neighborhood WorkLabel degree radius))))

noncomputable instance neighborhoodFintypeInstance
    (WorkLabel : Type) [Fintype WorkLabel] (degree radius : Nat) :
    Fintype (Neighborhood WorkLabel degree radius) :=
  neighborhoodFintype WorkLabel degree radius

noncomputable instance neighborhoodDecidableEqInstance
    (WorkLabel : Type) (degree radius : Nat) :
    DecidableEq (Neighborhood WorkLabel degree radius) :=
  Classical.decEq _


namespace View

def lookup {WorkLabel : Type} {degree : Nat} :
    (radius : Nat) → Neighborhood WorkLabel degree radius →
      (directions : List (Fin degree)) → directions.length ≤ radius →
      Option (Option WorkLabel)
  | 0, label, [], _ => some label
  | 0, _, _ :: _, impossible => by simp at impossible
  | radius + 1, view, [], _ => some view.1
  | radius + 1, view, direction :: directions, withinRadius =>
      (view.2 direction).bind fun child =>
        lookup radius child directions (Nat.le_of_succ_le_succ withinRadius)

def observe {WorkLabel : Type} {degree radius : Nat}
    (view : Neighborhood WorkLabel degree radius)
    (path : BoundedPath degree radius) : Option (Option WorkLabel) :=
  lookup radius view path.1 path.2

@[simp] theorem lookup_nil {WorkLabel : Type} {degree radius : Nat}
    (view : Neighborhood WorkLabel degree radius) :
    lookup radius view [] (by simp) = some
      (match radius, view with
       | 0, label => label
       | _ + 1, nodeView => nodeView.1) := by
  cases radius <;> rfl

theorem lookup_neighborhoodAt_eq_follow
    {WorkLabel : Type} {degree : Nat}
    (allNodes : List (Node WorkLabel degree)) {radius position : Nat}
    (directions : List (Fin degree))
    (withinRadius : directions.length ≤ radius) :
    (Scaffold.neighborhoodAt allNodes radius position).bind
        (fun view => lookup radius view directions withinRadius) =
      (Scaffold.follow allNodes position directions).bind fun endpoint =>
        allNodes[endpoint]?.map Node.label := by
  induction radius generalizing position directions with
  | zero =>
      cases directions with
      | nil =>
          cases nodeEq : allNodes[position]? <;>
            simp [Scaffold.neighborhoodAt, lookup, Scaffold.follow, nodeEq]
      | cons direction directions => simp at withinRadius
  | succ radius ih =>
      cases directions with
      | nil =>
          cases nodeEq : allNodes[position]? <;>
            simp [Scaffold.neighborhoodAt, lookup, Scaffold.follow, nodeEq]
      | cons direction directions =>
          have tailWithin : directions.length ≤ radius :=
            Nat.le_of_succ_le_succ withinRadius
          cases nodeEq : allNodes[position]? with
          | none =>
              simp [Scaffold.neighborhoodAt, lookup, Scaffold.follow, nodeEq]
          | some node =>
              cases edgeEq : node.edgeOffset direction with
              | none =>
                  simp [Scaffold.neighborhoodAt, lookup, Scaffold.follow,
                    nodeEq, edgeEq]
              | some offset =>
                  simpa [Scaffold.neighborhoodAt, lookup, Scaffold.follow,
                    nodeEq, edgeEq] using
                    ih (position := position + offset)
                      (directions := directions) tailWithin

theorem lookup_topNeighborhood_eq_follow
    {WorkLabel : Type} {degree : Nat}
    (scaffold : Scaffold WorkLabel degree)
    {radius : Nat} (directions : List (Fin degree))
    (withinRadius : directions.length ≤ radius) :
    lookup radius (scaffold.topNeighborhood radius) directions withinRadius =
      (Scaffold.follow scaffold.nodes 0 directions).bind fun position =>
        scaffold.nodes[position]?.map Node.label := by
  cases radius with
  | zero =>
      cases directions with
      | nil => simp [lookup, Scaffold.topNeighborhood, Scaffold.follow,
          Scaffold.nodes]
      | cons direction directions => simp at withinRadius
  | succ radius =>
      cases directions with
      | nil => simp [lookup, Scaffold.topNeighborhood, Scaffold.follow,
          Scaffold.nodes]
      | cons direction directions =>
          have tailWithin : directions.length ≤ radius :=
            Nat.le_of_succ_le_succ withinRadius
          cases edgeEq : scaffold.top.edgeOffset direction with
          | none =>
              simp [lookup, Scaffold.topNeighborhood, Scaffold.follow,
                Scaffold.nodes, edgeEq]
          | some offset =>
              simpa [lookup, Scaffold.topNeighborhood, Scaffold.follow,
                Scaffold.nodes, edgeEq] using
                lookup_neighborhoodAt_eq_follow scaffold.nodes
                  (position := offset) directions tailWithin

theorem ext_of_observe_eq
    {WorkLabel : Type} {degree radius : Nat}
    {left right : Neighborhood WorkLabel degree radius}
    (equal : ∀ path : BoundedPath degree radius,
      observe left path = observe right path) :
    left = right := by
  induction radius with
  | zero =>
      have root := equal (emptyPath degree 0)
      change Option WorkLabel at left right
      have root' : left = right := by
        simpa [observe, lookup, emptyPath] using root
      simpa only [Neighborhood] using root'
  | succ radius ih =>
      apply Prod.ext
      · have root := equal (emptyPath degree (radius + 1))
        exact Option.some.inj (by simpa [observe, lookup, emptyPath] using root)
      · funext direction
        cases leftChild : left.2 direction with
        | none =>
            cases rightChild : right.2 direction with
            | none => rfl
            | some child =>
                let childRoot : BoundedPath degree radius := emptyPath degree radius
                let parentPath : BoundedPath degree (radius + 1) :=
                  ⟨direction :: childRoot.1, by simp [childRoot]⟩
                have observed := equal parentPath
                simp [observe, lookup, parentPath, childRoot,
                  leftChild, rightChild] at observed
        | some leftView =>
            cases rightChild : right.2 direction with
            | none =>
                let childRoot : BoundedPath degree radius := emptyPath degree radius
                let parentPath : BoundedPath degree (radius + 1) :=
                  ⟨direction :: childRoot.1, by simp [childRoot]⟩
                have observed := equal parentPath
                simp [observe, lookup, parentPath, childRoot,
                  leftChild, rightChild] at observed
            | some rightView =>
                congr 1
                apply ih
                intro childPath
                let parentPath : BoundedPath degree (radius + 1) :=
                  ⟨direction :: childPath.1, by simp [childPath.2]⟩
                have observed := equal parentPath
                simpa [observe, lookup, parentPath, leftChild, rightChild] using observed

end View


namespace ScaffoldLemmas

theorem follow_append {WorkLabel : Type} {degree : Nat}
    (nodes : List (Node WorkLabel degree)) (position : Nat)
    (first second : List (Fin degree)) :
    Scaffolding.Scaffold.follow nodes position (first ++ second) =
      (Scaffolding.Scaffold.follow nodes position first).bind fun middle =>
        Scaffolding.Scaffold.follow nodes middle second := by
  induction first generalizing position with
  | nil =>
      cases nodeEq : nodes[position]? with
      | none =>
          cases second <;>
            simp [Scaffolding.Scaffold.follow, nodeEq]
      | some node => simp [Scaffolding.Scaffold.follow, nodeEq]
  | cons direction directions ih =>
      cases nodeEq : nodes[position]? with
      | none => simp [Scaffolding.Scaffold.follow, nodeEq]
      | some node =>
          cases edgeEq : node.edgeOffset direction with
          | none => simp [Scaffolding.Scaffold.follow, nodeEq, edgeEq]
          | some offset => simp [Scaffolding.Scaffold.follow, nodeEq, edgeEq, ih]

theorem follow_result_present {WorkLabel : Type} {degree : Nat}
    {nodes : List (Node WorkLabel degree)} {start endpoint : Nat}
    {directions : List (Fin degree)}
    (result : Scaffolding.Scaffold.follow nodes start directions = some endpoint) :
    nodes[endpoint]?.isSome := by
  induction directions generalizing start with
  | nil =>
      cases nodeEq : nodes[start]? with
      | none => simp [Scaffolding.Scaffold.follow, nodeEq] at result
      | some node =>
          have endpointEq : endpoint = start := by
            simpa [Scaffolding.Scaffold.follow, nodeEq] using result.symm
          subst endpoint
          simp [nodeEq]
  | cons direction directions ih =>
      cases nodeEq : nodes[start]? with
      | none => simp [Scaffolding.Scaffold.follow, nodeEq] at result
      | some node =>
          cases edgeEq : node.edgeOffset direction with
          | none => simp [Scaffolding.Scaffold.follow, nodeEq, edgeEq] at result
          | some offset =>
              exact ih (by simpa [Scaffolding.Scaffold.follow, nodeEq, edgeEq] using result)

theorem follow_result_lt_length {WorkLabel : Type} {degree : Nat}
    {nodes : List (Node WorkLabel degree)} {start endpoint : Nat}
    {directions : List (Fin degree)}
    (result : Scaffolding.Scaffold.follow nodes start directions = some endpoint) :
    endpoint < nodes.length := by
  have present := follow_result_present result
  by_contra notLess
  have outOfBounds : nodes.length ≤ endpoint := Nat.le_of_not_gt notLess
  have absent : nodes[endpoint]? = none := List.getElem?_eq_none outOfBounds
  simp [absent] at present

end ScaffoldLemmas


namespace PegGrammar

variable {Terminal : Type} [DecidableEq Terminal] {nonterminalCount : Nat}

theorem isLoffTotal_of_nonterminal_total
    (grammar : PegGrammar Terminal nonterminalCount)
    (nonterminalTotal : ∀ name input,
      ∃ result, grammar.Evaluates (.nonterminal name) input result) :
    grammar.IsLoffTotal := by
  intro expression
  induction expression with
  | empty => exact fun input => ⟨.success input, .empty input⟩
  | failure => exact fun input => ⟨.failure, .failure input⟩
  | terminal symbol => exact fun input =>
      ⟨PegSeparation.PegGrammar.terminalResult symbol input, .terminal symbol input⟩
  | nonterminal name => exact nonterminalTotal name
  | sequence left right leftIH rightIH =>
      intro input
      obtain ⟨leftResult, leftEvaluation⟩ := leftIH input
      cases leftResult with
      | failure => exact ⟨.failure, .sequenceFailure leftEvaluation⟩
      | success middle =>
          obtain ⟨rightResult, rightEvaluation⟩ := rightIH middle
          exact ⟨rightResult, .sequenceSuccess leftEvaluation rightEvaluation⟩
  | orderedChoice left right leftIH rightIH =>
      intro input
      obtain ⟨leftResult, leftEvaluation⟩ := leftIH input
      cases leftResult with
      | failure =>
          obtain ⟨rightResult, rightEvaluation⟩ := rightIH input
          exact ⟨rightResult, .choiceRight leftEvaluation rightEvaluation⟩
      | success remaining => exact ⟨.success remaining, .choiceLeft leftEvaluation⟩
  | notPredicate body bodyIH =>
      intro input
      obtain ⟨bodyResult, bodyEvaluation⟩ := bodyIH input
      cases bodyResult with
      | failure => exact ⟨.success input, .notSuccess bodyEvaluation⟩
      | success remaining => exact ⟨.failure, .notFailure bodyEvaluation⟩
  | andPredicate body bodyIH =>
      intro input
      obtain ⟨bodyResult, bodyEvaluation⟩ := bodyIH input
      cases bodyResult with
      | failure => exact ⟨.failure, .andFailure bodyEvaluation⟩
      | success remaining => exact ⟨.success input, .andSuccess bodyEvaluation⟩

end PegGrammar

end PegSeparation.SCAToPEG
