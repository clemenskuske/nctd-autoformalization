import Lax16.PlanarGraphs
import Lax16.TeachingMaps

/-!
---
title: An outerplanar neighbor layer with ambient twin witnesses
type: theorem
---
Let `U` be a set of neighbors of a vertex `v₀`, and suppose the graph induced
by `U` is outerplanar.  The vertices of `U` have positive ambient teaching
sets of size at most three which separate every pair whose closed
neighborhoods differ in the ambient graph.  Witnesses repairing closed twins
of the induced graph may lie outside `U`.

Adding the common anchor `v₀` gives sets of size at most four and certifies
every layer vertex against all vertices outside the closed neighborhood of
`v₀`.
-/

namespace Lax16.OuterplanarLayer

open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u

/-- A width-three positive assignment separating all ambient concepts in `U`. -/
def IsLayerAssignment {V : Type u} (G : SimpleGraph V)
    (U : Finset V) (S : TeachingMap V 1) : Prop :=
  (∀ w : V, w ∈ U →
    (S w).card ≤ 3 ∧
    ∀ x ∈ S w, x ∈ closedBall G 1 w) ∧
  ∀ w₁ w₂ : V, w₁ ∈ U → w₂ ∈ U →
    DistinctConcepts G 1 w₁ w₂ →
      Separates G 1 S w₁ w₂

/-- Add a common anchor to every teaching set. -/
noncomputable def anchoredTeaching {V : Type u} (v₀ : V)
    (S : TeachingMap V 1) : TeachingMap V 1 := by
  classical
  exact fun w => insert v₀ (S w)

/-- The outerplanar layer assignment exists and gains external certification when anchored. -/
axiom exists_outerplanar_layer_assignment {V : Type u} [Fintype V]
    (G : SimpleGraph V) (v₀ : V) (U : Finset V)
    (hneighbors : ∀ w ∈ U, G.Adj v₀ w)
    (houter : IsOuterplanar (G.induce (↑U : Set V))) :
    ∃ S : TeachingMap V 1,
      IsLayerAssignment G U S ∧
      (∀ w : V, w ∈ U →
        (anchoredTeaching v₀ S w).card ≤ 4 ∧
        ∀ y ∈ anchoredTeaching v₀ S w, y ∈ closedBall G 1 w) ∧
      ∀ w : V, w ∈ U → ∀ x : V, x ∉ closedBall G 1 v₀ →
        ∃ y ∈ anchoredTeaching v₀ S w, y ∉ closedBall G 1 x

end Lax16.OuterplanarLayer
