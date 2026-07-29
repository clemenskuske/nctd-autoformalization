import Mathlib.Combinatorics.SimpleGraph.Finite
import Lax16.BatchFramework
import Lax16.PlanarGraphs

/-!
---
title: An admissible batch around a high-degree planar vertex
type: theorem
---
Let `v` be a vertex of degree at least four in a finite planar graph.  There
is an admissible radius-one batch of width four which contains the whole
closed neighborhood of `v` and at most one additional outside vertex.
-/

namespace Lax16.PlanarVertexBatch

open Lax16.BatchFramework
open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u

/-- Every high-degree planar center has the required width-four batch. -/
axiom exists_planar_vertex_batch {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hplanar : IsPlanar G)
    (v : V) (hdegree : 4 ≤ (G.neighborSet v).ncard) :
    ∃ B : BatchAssignment G,
      closedBallFinset G 1 v ⊆ B.vertices ∧
      (B.vertices \ closedBallFinset G 1 v).card ≤ 1 ∧
      IsAdmissible G 4 B

end Lax16.PlanarVertexBatch
