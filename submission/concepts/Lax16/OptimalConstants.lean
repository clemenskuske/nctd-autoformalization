import Lax16.PlanarGraphs
import Lax16.TeachingMaps

/-!
---
title: Optimal positive NCTD constants for planar and outerplanar graphs
type: theorem
---
At radius one, four is the optimal uniform positive no-clash teaching bound
for finite planar graphs, and two is the optimal uniform bound for finite
outerplanar graphs.
-/

namespace Lax16.OptimalConstants

open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u

/-- The planar and outerplanar radius-one constants are respectively four and two. -/
axiom optimal_radius_one_constants :
    (∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      IsPlanar G → positiveNCTD G 1 ≤ 4) ∧
    (∃ G : SimpleGraph (Fin 5),
      IsPlanar G ∧ positiveNCTD G 1 = 4) ∧
    (∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      IsOuterplanar G → positiveNCTD G 1 ≤ 2) ∧
    ∃ G : SimpleGraph (Fin 6),
      IsOuterplanar G ∧ positiveNCTD G 1 = 2

end Lax16.OptimalConstants
