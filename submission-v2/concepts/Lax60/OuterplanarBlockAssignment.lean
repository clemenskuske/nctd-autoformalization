import Lax60.PlanarGraphs
import Lax60.TeachingMaps

/-!
---
title: Two-connected outerplanar graphs admit two-label teaching maps
type: theorem
---
Every finite two-connected outerplanar graph admits a positive radius-one
no-clash teaching map in which every vertex receives exactly two distinct
labels.  This is the block lemma used to assemble the sharp outerplanar
bound.
-/

namespace Lax60.OuterplanarBlockAssignment

open Lax60.PlanarGraphs
open Lax60.TeachingMaps

universe u

/-- A two-connected outerplanar graph has an exact two-label positive map. -/
axiom exists_two_label_assignment {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (houter : IsOuterplanar G)
    (htwo : IsTwoConnected G) :
    ∃ T : TeachingMap V 1,
      IsPositive G 1 T ∧
      IsNoClash G 1 T ∧
      ∀ v : V, (T v).card = 2

end Lax60.OuterplanarBlockAssignment
