import Mathlib.Combinatorics.SimpleGraph.Finite
import Lax16.DominatorDefinitions
import Lax16.PlanarGraphs

/-!
---
title: Two dominators at a degree-four center
type: theorem
---
Suppose a planar center `v` has exactly four neighbors and exactly two of
them, `w₁` and `w₂`, dominate it.  The active members of this pair can be
assigned valid anchored teaching sets of size at most four simultaneously.
Each set handles non-active concepts in the center ball; the pair itself may
be separated by a label from either set.  The two remaining neighbors are
nonadjacent and supply the spare internal witnesses.
-/

namespace Lax16.TwoDominators

open Lax16.DominatorDefinitions
open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u

/-- The exceptional pair of degree-four dominators can be completed together. -/
axiom exists_two_dominator_assignment {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hplanar : IsPlanar G)
    (v w₁ w₂ : V)
    (hdegree : (G.neighborSet v).ncard = 4)
    (hne : w₁ ≠ w₂)
    (hdom : dominatorSet G v = {w₁, w₂}) :
    ∃ T : TeachingMap V 1, CompletesActiveDominators G v T

end Lax16.TwoDominators
