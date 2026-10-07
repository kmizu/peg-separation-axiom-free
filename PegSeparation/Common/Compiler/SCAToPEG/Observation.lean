import PegSeparation.Common.Compiler.SCAToPEG.History


namespace PegSeparation.SCAToPEG

open PegSeparation
open PegSeparation.Scaffolding

section Observation

variable {Terminal : Type}
variable {stateCount workLabelCount degree radius : Nat}

theorem observe_reverseConfig_eq_follow_bind
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) (path : BoundedPath degree radius) :
    View.observe
        ((reverseConfig automaton input).2.topNeighborhood radius) path =
      (Scaffold.follow (reverseConfig automaton input).2.nodes 0 path.1).bind
        (fun endpoint =>
          some (reverseConfig automaton (input.drop endpoint)).2.top.label) := by
  unfold View.observe
  rw [View.lookup_topNeighborhood_eq_follow]
  cases followed :
      Scaffold.follow (reverseConfig automaton input).2.nodes 0 path.1 with
  | none => simp
  | some endpoint =>
      simpa only [Option.bind_some] using
        reverseConfig_endpoint_label automaton input path.1 endpoint followed

theorem observe_reverseConfig_eq_follow_map
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) (path : BoundedPath degree radius) :
    View.observe
        ((reverseConfig automaton input).2.topNeighborhood radius) path =
      (Scaffold.follow (reverseConfig automaton input).2.nodes 0 path.1).map
        (fun endpoint =>
          (reverseConfig automaton (input.drop endpoint)).2.top.label) := by
  rw [observe_reverseConfig_eq_follow_bind]
  cases Scaffold.follow (reverseConfig automaton input).2.nodes 0 path.1 <;>
    rfl

theorem observe_reverseConfig_eq_none_iff
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) (path : BoundedPath degree radius) :
    View.observe
        ((reverseConfig automaton input).2.topNeighborhood radius) path = none ↔
      Scaffold.follow (reverseConfig automaton input).2.nodes 0 path.1 = none := by
  rw [observe_reverseConfig_eq_follow_bind]
  cases Scaffold.follow (reverseConfig automaton input).2.nodes 0 path.1 <;> simp

theorem observe_reverseConfig_of_follow
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) (path : BoundedPath degree radius) (endpoint : Nat)
    (followed :
      Scaffold.follow (reverseConfig automaton input).2.nodes 0 path.1 =
        some endpoint) :
    View.observe
        ((reverseConfig automaton input).2.topNeighborhood radius) path =
      some (reverseConfig automaton (input.drop endpoint)).2.top.label := by
  rw [observe_reverseConfig_eq_follow_bind, followed]
  rfl

theorem observe_reverseConfig_eq_some_iff
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) (path : BoundedPath degree radius)
    (label : Option (Fin workLabelCount)) :
    View.observe
        ((reverseConfig automaton input).2.topNeighborhood radius) path =
        some label ↔
      ∃ endpoint,
        Scaffold.follow (reverseConfig automaton input).2.nodes 0 path.1 =
          some endpoint ∧
        (reverseConfig automaton (input.drop endpoint)).2.top.label = label := by
  rw [observe_reverseConfig_eq_follow_bind]
  constructor
  · intro equality
    cases followed :
        Scaffold.follow (reverseConfig automaton input).2.nodes 0 path.1 with
    | none => simp [followed] at equality
    | some endpoint =>
        have labelEq :
            (reverseConfig automaton (input.drop endpoint)).2.top.label =
              label := by
          exact Option.some.inj (by simpa [followed] using equality)
        exact ⟨endpoint, rfl, labelEq⟩
  · rintro ⟨endpoint, followed, labelEq⟩
    rw [followed]
    exact congrArg some labelEq

theorem observe_reverseConfig_eq_some_none_iff
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) (path : BoundedPath degree radius) :
    View.observe
        ((reverseConfig automaton input).2.topNeighborhood radius) path =
        some none ↔
      ∃ endpoint,
        Scaffold.follow (reverseConfig automaton input).2.nodes 0 path.1 =
          some endpoint ∧
        (reverseConfig automaton (input.drop endpoint)).2.top.label = none := by
  exact observe_reverseConfig_eq_some_iff automaton input path none

theorem observe_reverseConfig_eq_some_some_iff
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal) (path : BoundedPath degree radius)
    (label : Fin workLabelCount) :
    View.observe
        ((reverseConfig automaton input).2.topNeighborhood radius) path =
        some (some label) ↔
      ∃ endpoint,
        Scaffold.follow (reverseConfig automaton input).2.nodes 0 path.1 =
          some endpoint ∧
        (reverseConfig automaton (input.drop endpoint)).2.top.label =
          some label := by
  exact observe_reverseConfig_eq_some_iff automaton input path (some label)

theorem reverseConfig_topNeighborhood_eq_iff_observe_eq
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal)
    (expected : Neighborhood (Fin workLabelCount) degree radius) :
    (reverseConfig automaton input).2.topNeighborhood radius = expected ↔
      ∀ path : BoundedPath degree radius,
        View.observe
            ((reverseConfig automaton input).2.topNeighborhood radius) path =
          View.observe expected path := by
  constructor
  · rintro rfl path
    rfl
  · exact View.ext_of_observe_eq

theorem reverseConfig_topNeighborhood_eq_iff_observe_eq_on_univ
    (automaton : Automaton Terminal stateCount workLabelCount degree radius)
    (input : List Terminal)
    (expected : Neighborhood (Fin workLabelCount) degree radius) :
    (reverseConfig automaton input).2.topNeighborhood radius = expected ↔
      ∀ path ∈ (Finset.univ : Finset (BoundedPath degree radius)),
        View.observe
            ((reverseConfig automaton input).2.topNeighborhood radius) path =
          View.observe expected path := by
  rw [reverseConfig_topNeighborhood_eq_iff_observe_eq]
  simp

end Observation

end PegSeparation.SCAToPEG
