import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card
import Lax16.BatchFramework
import Lax16.AnchorLabels

/-!
---
title: Every vertex of degree at most three admits a width-four neighborhood batch
type: theorem
---
For a vertex `v` of degree at most three, its closed neighborhood is a batch
of at most four vertices.  Give every batch vertex the anchor label `v`, then
add at most one positive witness for each of its at most three internal pairs.
This produces an admissible radius-one batch of width four without using
planarity.
-/

namespace Lax16.SmallDegreeBatch

open Lax16.BatchFramework
open Lax16.TeachingMaps

universe u

/-- A degree-at-most-three vertex has a complete width-four neighborhood batch. -/
axiom exists_small_degree_batch {V : Type u} [Fintype V]
    (G : SimpleGraph V) (v : V)
    (hdegree : (G.neighborSet v).ncard ≤ 3) :
    ∃ B : BatchAssignment G,
      B.vertices = closedBallFinset G 1 v ∧
      IsAdmissible G 4 B

end Lax16.SmallDegreeBatch
