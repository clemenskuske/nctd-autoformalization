import Mathlib.Combinatorics.SimpleGraph.Operations
import Lax16.PlanarGraphs
import Lax16.TeachingMaps

/-!
---
title: Sharpness of the outerplanar bound
type: theorem
---
Let `H` be the six-vertex graph formed from two triangles
`0-1-2-0` and `3-4-5-3` together with the edges `0-3` and `1-4`.
This graph is outerplanar, and both its ordinary and positive radius-one
no-clash teaching dimensions are exactly two.
-/

namespace Lax16.OuterplanarSharpness

open Lax16.PlanarGraphs
open Lax16.TeachingMaps

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

/-- The six-vertex example is outerplanar and has both dimensions exactly two. -/
axiom outerplanar_bound_is_sharp :
    IsOuterplanar sharpOuterplanarGraph ∧
    nctd sharpOuterplanarGraph 1 = 2 ∧
    positiveNCTD sharpOuterplanarGraph 1 = 2

end Lax16.OuterplanarSharpness
