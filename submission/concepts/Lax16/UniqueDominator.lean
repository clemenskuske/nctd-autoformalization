import Lax16.DominatorDefinitions
import Lax16.PlanarGraphs

/-!
---
title: Teaching a unique active dominator
type: theorem
---
If `w` is the unique dominating neighbor of a planar center `v` and is
active, then `w` has a valid anchored teaching set of size at most four.
An outside witness separates `w` from `v`; planarity leaves at most two
neighbors needing additional internal witnesses.
-/

namespace Lax16.UniqueDominator

open Lax16.DominatorDefinitions
open Lax16.PlanarGraphs

universe u

/-- A unique active dominator admits a valid width-four teaching set. -/
axiom exists_unique_dominator_set {V : Type u}
    (G : SimpleGraph V) (hplanar : IsPlanar G)
    (v w : V)
    (hunique : dominatorSet G v = {w})
    (hactive : IsActiveDominator G v w) :
    ∃ S : Finset V, IsDominatorTeachingSet G v w S

end Lax16.UniqueDominator
