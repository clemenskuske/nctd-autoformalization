import Lax16.PlanarGraphs
import Lax16.TeachingMaps

/-!
---
title: Two-label assignments on two-connected outerplanar graphs
type: theorem
---
Every finite two-connected outerplanar graph admits a positive radius-one
no-clash teaching map in which every vertex receives exactly two distinct
labels.  This is the block lemma used to assemble the sharp outerplanar
bound.
-/

namespace Lax16.OuterplanarBlockAssignment

open Lax16.PlanarGraphs
open Lax16.TeachingMaps

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

end Lax16.OuterplanarBlockAssignment
