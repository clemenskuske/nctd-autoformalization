import Lax60.PlanarGraphs
import Lax60.TeachingMaps

/-!
---
title: Outerplanar graphs have positive NCTD at most two
type: theorem
---
Every finite outerplanar graph has positive no-clash teaching dimension at
most two for closed neighborhoods, equivalently for closed balls of radius
one.
-/

namespace Lax60.OuterplanarBound

open Lax60.PlanarGraphs
open Lax60.TeachingMaps

universe u

/-- The sharp radius-one positive upper bound for outerplanar graphs. -/
axiom positiveNCTD_le_two {V : Type u} [Fintype V]
    (G : SimpleGraph V) (houter : IsOuterplanar G) :
    positiveNCTD G 1 ≤ 2

end Lax60.OuterplanarBound
