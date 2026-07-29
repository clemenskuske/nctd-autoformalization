import Lax16.PlanarGraphs
import Lax16.TeachingMaps

/-!
---
title: The outside three-set gadget
type: theorem
---
Let `Y` be three neighbors of a vertex `v` in a planar graph.  At most one
vertex outside the closed neighborhood of `v` is adjacent to every member of
`Y`.  If such a vertex `x` is included in the batch and receives
`{x} ∪ Y`, this teaching set is positive, has size at most four, and certifies
`x` against every vertex outside the enlarged batch.
-/

namespace Lax16.OutsideThreeSetGadget

open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u

/-- An outside vertex adjacent to all three selected neighbors. -/
def OutsideSees {V : Type u} (G : SimpleGraph V)
    (v : V) (Y : Finset V) (x : V) : Prop :=
  x ∉ closedBall G 1 v ∧ ∀ y ∈ Y, G.Adj x y

/-- Uniqueness and external certification of the possible outside obstruction. -/
axiom outside_three_set_gadget {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hplanar : IsPlanar G)
    (v : V) (Y : Finset V)
    (hcard : Y.card = 3)
    (hneighbors : ∀ y ∈ Y, G.Adj v y) :
    Set.Subsingleton {x : V | OutsideSees G v Y x} ∧
    ∀ x : V, OutsideSees G v Y x →
      (∀ y ∈ insert x Y, y ∈ closedBall G 1 x) ∧
      (insert x Y).card ≤ 4 ∧
      ∀ z : V, z ∉ insert x (closedBallFinset G 1 v) →
        ∃ y ∈ insert x Y, y ∉ closedBall G 1 z

end Lax16.OutsideThreeSetGadget
