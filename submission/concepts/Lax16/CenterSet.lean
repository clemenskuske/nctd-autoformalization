import Mathlib.Combinatorics.SimpleGraph.Finite
import Lax16.PlanarGraphs
import Lax16.TeachingMaps

/-!
---
title: A four-label center set in a planar neighborhood
type: theorem
---
Let `v` be a planar-graph vertex with at least four neighbors.  There is a
four-element set `W` of neighbors such that every neighbor which does not
dominate `v` misses some element of `W`.  Thus `W`, used as the teaching set
of `v`, separates the center from every non-dominating neighbor.
-/

namespace Lax16.CenterSet

open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u

/-- Four neighbor labels separate the center from every non-dominator. -/
axiom exists_center_set {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hplanar : IsPlanar G)
    (v : V) (hdegree : 4 ≤ (G.neighborSet v).ncard) :
    ∃ W : Finset V,
      W.card = 4 ∧
      (∀ w ∈ W, G.Adj v w) ∧
      ∀ w : V, G.Adj v w → ¬ Dominates G 1 v w →
        ∃ x ∈ W, x ∉ closedBall G 1 w

end Lax16.CenterSet
