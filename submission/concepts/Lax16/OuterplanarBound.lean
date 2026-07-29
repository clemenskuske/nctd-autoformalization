import Lax16.PlanarGraphs
import Lax16.TeachingMaps

/-!
---
title: Outerplanar graphs have positive NCTD at most two
type: theorem
---
Every finite outerplanar graph has positive no-clash teaching dimension at
most two for closed neighborhoods, equivalently for closed balls of radius
one.
-/

namespace Lax16.OuterplanarBound

open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u

/-- The sharp radius-one positive upper bound for outerplanar graphs. -/
axiom positiveNCTD_le_two {V : Type u} [Fintype V]
    (G : SimpleGraph V) (houter : IsOuterplanar G) :
    positiveNCTD G 1 ≤ 2

end Lax16.OuterplanarBound
