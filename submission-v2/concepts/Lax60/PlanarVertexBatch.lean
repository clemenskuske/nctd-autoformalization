import Mathlib.Combinatorics.SimpleGraph.Finite
import Lax60.BatchFramework
import Lax60.PlanarGraphs

/-!
---
title: Every planar vertex with at least four neighbors admits a width-four batch
type: theorem
---
Let `v` be a vertex of degree at least four in a finite planar graph.  There
is an admissible radius-one batch of width four which contains the whole
closed neighborhood of `v` and at most one additional outside vertex.
-/

namespace Lax60.PlanarVertexBatch

open Lax60.BatchFramework
open Lax60.PlanarGraphs
open Lax60.TeachingMaps

universe u

/-- Every high-degree planar center has the required width-four batch. -/
axiom exists_planar_vertex_batch_of_degree_ge_four {V : Type u}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hplanar : IsPlanar G)
    (v : V) (hdegree : 4 ≤ (G.neighborSet v).ncard) :
    ∃ B : BatchAssignment G,
      closedBallFinset G 1 v ⊆ B.vertices ∧
      (B.vertices \ closedBallFinset G 1 v).card ≤ 1 ∧
      IsAdmissible G 4 B

end Lax60.PlanarVertexBatch
