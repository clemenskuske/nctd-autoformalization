import Mathlib.Combinatorics.SimpleGraph.Operations
import Lax60.PlanarGraphs
import Lax60.TeachingMaps

/-!
---
title: Some outerplanar graph has positive NCTD at least two
type: theorem
---
Let `H` be the six-vertex graph formed from two triangles
`0-1-2-0` and `3-4-5-3` together with the edges `0-3` and `1-4`.

![The graph H: two triangles joined by the edges 0-3 and 1-4.](https://raw.githubusercontent.com/clemenskuske/nctd-autoformalization/dc07f80a4cc903ff619213dfa9e97f50ac8449b8/figures/lax-60/sharp-outerplanar-graph.svg)

*The outerplanar sharpness graph `H`.*

This graph is outerplanar and witnesses that the positive radius-one
no-clash teaching dimension of outerplanar graphs cannot be below two.
-/

namespace Lax60.OuterplanarSharpness

open Lax60.PlanarGraphs
open Lax60.TeachingMaps

/-- Two triangles joined by two matching edges, with the third matching edge absent. -/
def sharpOuterplanarGraph : SimpleGraph (Fin 6) :=
  SimpleGraph.edge 0 1 ⊔
  SimpleGraph.edge 1 2 ⊔
  SimpleGraph.edge 2 0 ⊔
  SimpleGraph.edge 3 4 ⊔
  SimpleGraph.edge 4 5 ⊔
  SimpleGraph.edge 5 3 ⊔
  SimpleGraph.edge 0 3 ⊔
  SimpleGraph.edge 1 4

/-- The six-vertex example is outerplanar and has positive NCTD at least two. -/
axiom positiveNCTD_ge_two :
    IsOuterplanar sharpOuterplanarGraph ∧
      2 ≤ positiveNCTD sharpOuterplanarGraph 1

end Lax60.OuterplanarSharpness
