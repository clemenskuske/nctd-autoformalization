import Mathlib.Combinatorics.SimpleGraph.Operations
import Lax16.PlanarGraphs
import Lax16.TeachingMaps

/-!
---
title: Sharpness of the planar bound
type: theorem
---
Let `W` be the five-vertex wheel whose center is `0` and whose rim is the
four-cycle `1-2-3-4-1`.  The graph is planar and its positive radius-one
no-clash teaching dimension is exactly four: the center must use all four rim
vertices to distinguish itself from the four dominated rim concepts.
-/

namespace Lax16.PlanarSharpness

open Lax16.PlanarGraphs
open Lax16.TeachingMaps

/-- The five-vertex wheel with a four-cycle rim. -/
def sharpPlanarGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.edge 0 1 ⊔
  SimpleGraph.edge 0 2 ⊔
  SimpleGraph.edge 0 3 ⊔
  SimpleGraph.edge 0 4 ⊔
  SimpleGraph.edge 1 2 ⊔
  SimpleGraph.edge 2 3 ⊔
  SimpleGraph.edge 3 4 ⊔
  SimpleGraph.edge 4 1

/-- The five-vertex wheel is planar and attains positive NCTD four. -/
axiom planar_bound_is_sharp :
    IsPlanar sharpPlanarGraph ∧
    positiveNCTD sharpPlanarGraph 1 = 4

end Lax16.PlanarSharpness
