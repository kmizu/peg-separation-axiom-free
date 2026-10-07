import PegSeparation.Common.Model.Scaffolding


namespace PegSeparation.External.LoffScaffoldView

open PegSeparation
open PegSeparation.Scaffolding
open PegSeparation.Scaffolding.Scaffold

namespace View

variable {WorkLabel : Type} {degree : Nat}

def labelAt (allNodes : List (Scaffolding.Node WorkLabel degree))
    (position : Nat) : Option WorkLabel := do
  let node ← allNodes[position]?
  node.label

def viewLabel {Work : Type} {degree : Nat} :
    (radius : Nat) → Scaffolding.Neighborhood Work degree radius →
      List (Fin degree) → Option Work
  | 0, label, [] => label
  | 0, _, _ :: _ => none
  | _ + 1, view, [] => view.1
  | radius + 1, view, direction :: directions => do
      let child ← view.2 direction
      viewLabel radius child directions

theorem viewLabel_neighborhoodAt_eq_follow
    (allNodes : List (Scaffolding.Node WorkLabel degree))
    {radius position : Nat} (directions : List (Fin degree))
    (hlength : directions.length ≤ radius) :
    (neighborhoodAt allNodes radius position).bind
        (fun view ↦ viewLabel radius view directions) =
      (follow allNodes position directions).bind (labelAt allNodes) := by
  induction radius generalizing position directions with
  | zero =>
      cases directions with
      | nil =>
          cases hnode : allNodes[position]? <;>
            simp [neighborhoodAt, follow, labelAt, hnode,
              viewLabel]
      | cons direction directions =>
          simp at hlength
  | succ radius ih =>
      cases directions with
      | nil =>
          cases hnode : allNodes[position]? <;>
            simp [neighborhoodAt, follow, labelAt, hnode,
              viewLabel]
      | cons direction directions =>
          have htail : directions.length ≤ radius := by
            simpa using Nat.succ_le_succ_iff.mp hlength
          cases hnode : allNodes[position]? with
          | none =>
              simp [neighborhoodAt, follow, hnode,
                viewLabel]
          | some node =>
              cases hoffset : node.edgeOffset direction with
              | none =>
                  simp [neighborhoodAt, follow, hnode, hoffset,
                    viewLabel]
              | some offset =>
                  simpa [neighborhoodAt, follow, hnode, hoffset,
                    viewLabel] using
                    ih (position := position + offset) directions htail

theorem viewLabel_topNeighborhood_eq_follow
    (scaffold : Scaffolding.Scaffold WorkLabel degree)
    {radius : Nat} (directions : List (Fin degree))
    (hlength : directions.length ≤ radius) :
    viewLabel radius
        (scaffold.topNeighborhood radius) directions =
      (follow scaffold.nodes 0 directions).bind (labelAt scaffold.nodes) := by
  cases radius with
  | zero =>
      cases directions with
      | nil =>
          simp [viewLabel,
            topNeighborhood, follow, nodes, labelAt]
      | cons direction directions =>
          simp at hlength
  | succ radius =>
      cases directions with
      | nil =>
          simp [viewLabel,
            topNeighborhood, follow, nodes, labelAt]
      | cons direction directions =>
          have htail : directions.length ≤ radius := by
            simpa using Nat.succ_le_succ_iff.mp hlength
          cases hoffset : scaffold.top.edgeOffset direction with
          | none =>
              simp [viewLabel,
                topNeighborhood, follow, nodes, hoffset]
          | some offset =>
              simpa [viewLabel,
                topNeighborhood, follow, nodes, hoffset] using
                viewLabel_neighborhoodAt_eq_follow scaffold.nodes
                  (position := offset) directions htail

end View

end PegSeparation.External.LoffScaffoldView
