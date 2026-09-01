import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card
import Lax60.DominatorDefinitions
import Lax60.PlanarGraphs

/-!
---
title: A planar center has at most one dominator above degree four and at most two in degree four
type: theorem
---
A planar vertex with at least five neighbors has at most one dominating
neighbor.  A planar vertex of degree four has at most two.  Three suitable
neighbors together with the center and two dominators would form a
`K₃,₃`; in the degree-four exception, three dominators would form a `K₅`.
-/

namespace Lax60.DominatorCount

open Lax60.DominatorDefinitions
open Lax60.PlanarGraphs

universe u

/-- The high-degree and degree-four bounds on the number of dominators. -/
axiom dominator_count_bounds {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hplanar : IsPlanar G) (v : V) :
    (5 ≤ (G.neighborSet v).ncard → (dominatorSet G v).ncard ≤ 1) ∧
    ((G.neighborSet v).ncard = 4 → (dominatorSet G v).ncard ≤ 2)

end Lax60.DominatorCount
