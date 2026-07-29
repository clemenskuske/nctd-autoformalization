import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Lax16.TeachingMaps

/-!
---
title: Componentwise gluing of nonempty teaching maps
type: theorem
---
Suppose every connected component of a finite graph has a positive
radius-one no-clash teaching map of width at most `d`, and every teaching set
is nonempty.  Combining these component maps gives such a map on the whole
graph: any nonempty label assigned in one component is absent from every ball
in another component.
-/

namespace Lax16.ComponentReduction

open Lax16.TeachingMaps

universe u

/-- Nonempty component maps of uniform width glue to a global positive map. -/
axiom combine_components {V : Type u} [Fintype V]
    (G : SimpleGraph V) (d : ℕ)
    (hcomponents :
      ∀ C : G.ConnectedComponent,
        ∃ T : TeachingMap C 1,
          IsPositive C.toSimpleGraph 1 T ∧
          IsNoClash C.toSimpleGraph 1 T ∧
          HasWidthAtMost T d ∧
          HasNonemptySets T) :
    HasPositiveNCTDAtMost G 1 d

end Lax16.ComponentReduction
