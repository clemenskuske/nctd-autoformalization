import Lax60.PlanarGraphs
import Lax60.TeachingMaps

/-!
---
title: Planar graphs have positive NCTD at most four
type: theorem
---
Every finite planar graph has positive no-clash teaching dimension at most
four for closed neighborhoods, equivalently for closed balls of radius one.
-/

namespace Lax60.PlanarBound

open Lax60.PlanarGraphs
open Lax60.TeachingMaps

universe u

/-- The radius-one positive upper bound for planar graphs. -/
axiom positiveNCTD_le_four {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hplanar : IsPlanar G) :
    positiveNCTD G 1 ≤ 4

end Lax60.PlanarBound
