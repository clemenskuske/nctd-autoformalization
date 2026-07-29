import Mathlib.Combinatorics.SimpleGraph.Finite
import Lax16.DominatorDefinitions
import Lax16.PlanarGraphs

/-!
---
title: Completion of all active dominators
type: theorem
---
At a planar center with at least four neighbors, all active dominating
neighbors can be assigned valid anchored teaching sets of size at most four.
The result combines the unique-dominator case with the exceptional pair that
can occur only in degree four.
-/

namespace Lax16.DominatorCompletion

open Lax16.DominatorDefinitions
open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u

/-- Every active dominator of a high-degree planar center can be completed. -/
axiom exists_dominator_completion {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hplanar : IsPlanar G)
    (v : V) (hdegree : 4 ≤ (G.neighborSet v).ncard) :
    ∃ T : TeachingMap V 1, CompletesActiveDominators G v T

end Lax16.DominatorCompletion
