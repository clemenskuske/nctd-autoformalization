import Mathlib.Combinatorics.SimpleGraph.Operations
import Lax60.PlanarGraphs
import Lax60.TeachingMaps

/-!
---
title: Some planar graph has positive NCTD at least four
type: theorem
---
Let `W` be the five-vertex wheel whose center is `0` and whose rim is the
four-cycle `1-2-3-4-1`.

![The wheel W: center 0 joined to the four-cycle 1-2-3-4-1.](https://raw.githubusercontent.com/clemenskuske/nctd-autoformalization/dc07f80a4cc903ff619213dfa9e97f50ac8449b8/figures/lax-60/sharp-planar-graph.svg)

*The planar sharpness graph `W`.*

The graph is planar and its positive radius-one
no-clash teaching dimension is at least four: the center must use all four
rim vertices to distinguish itself from the four dominated rim concepts.
-/

namespace Lax60.PlanarSharpness

open Lax60.PlanarGraphs
open Lax60.TeachingMaps

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

/-- The five-vertex wheel is planar and has positive NCTD at least four. -/
axiom positiveNCTD_ge_four :
    IsPlanar sharpPlanarGraph ∧
      4 ≤ positiveNCTD sharpPlanarGraph 1

end Lax60.PlanarSharpness
