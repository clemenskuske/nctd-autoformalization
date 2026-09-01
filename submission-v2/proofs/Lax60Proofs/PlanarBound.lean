import Lax60.BatchFramework
import Lax60.BatchReassignment
import Lax60.PlanarBound
import Lax60.PlanarVertexBatch
import Lax60.SmallDegreeBatch

namespace Lax60Proofs.PlanarBound

open Lax60.BatchFramework
open Lax60.PlanarGraphs
open Lax60.TeachingMaps

universe u

/--
---
conclusion: Lax60.PlanarBound.positiveNCTD_le_four
assumptions:
  - Lax60.BatchReassignment.reassignment
  - Lax60.PlanarVertexBatch.exists_planar_vertex_batch_of_degree_ge_four
  - Lax60.SmallDegreeBatch.exists_small_degree_batch
---
Choose an admissible batch centered at each vertex.  The schedule is indexed
by all vertices, and the last batch of a vertex is the largest index of a
batch containing it.  This construction also handles an empty vertex type:
all vertex-indexed obligations are then vacuous.
-/
theorem positiveNCTD_le_four {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hplanar : IsPlanar G) :
    positiveNCTD G 1 ≤ 4 := by
  classical
  have hcenter (v : V) : v ∈ closedBallFinset G 1 v := by
    simp only [closedBallFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      closedBall, Set.mem_setOf_eq]
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  have hexistsBatch :
      ∀ v : V, ∃ B : BatchAssignment G,
        v ∈ B.vertices ∧ IsAdmissible G 4 B := by
    intro v
    by_cases hdegree : (G.neighborSet v).ncard ≤ 3
    · rcases Lax60.SmallDegreeBatch.exists_small_degree_batch G v hdegree with
        ⟨B, hvertices, hadmissible⟩
      refine ⟨B, ?_, hadmissible⟩
      rw [hvertices]
      exact hcenter v
    · have hdegree' : 4 ≤ (G.neighborSet v).ncard := by omega
      rcases Lax60.PlanarVertexBatch.exists_planar_vertex_batch_of_degree_ge_four
          G hplanar v hdegree' with ⟨B, hcontains, _, hadmissible⟩
      exact ⟨B, hcontains (hcenter v), hadmissible⟩
  let chosenBatch : V → BatchAssignment G :=
    fun v => Classical.choose (hexistsBatch v)
  have chosenBatch_mem (v : V) : v ∈ (chosenBatch v).vertices :=
    (Classical.choose_spec (hexistsBatch v)).1
  have chosenBatch_admissible (v : V) :
      IsAdmissible G 4 (chosenBatch v) :=
    (Classical.choose_spec (hexistsBatch v)).2
  let vertexIndex : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let containingIndices (v : V) : Finset (Fin (Fintype.card V)) :=
    Finset.univ.filter fun i =>
      v ∈ (chosenBatch (vertexIndex.symm i)).vertices
  have containingIndices_nonempty (v : V) :
      (containingIndices v).Nonempty := by
    refine ⟨vertexIndex v, ?_⟩
    simp [containingIndices, chosenBatch_mem]
  let lastIndex (v : V) : Fin (Fintype.card V) :=
    (containingIndices v).max' (containingIndices_nonempty v)
  let schedule : BatchSchedule G :=
    { batchCount := Fintype.card V
      batch := fun i => chosenBatch (vertexIndex.symm i)
      last := lastIndex
      mem_last := by
        intro v
        have hmem := Finset.max'_mem
          (containingIndices v) (containingIndices_nonempty v)
        simpa [containingIndices, lastIndex] using hmem
      last_is_last := by
        intro v i hmem
        apply Finset.le_max' (containingIndices v) i
        simp [containingIndices, hmem] }
  have hallAdmissible :
      ∀ i : Fin schedule.batchCount,
        IsAdmissible G 4 (schedule.batch i) := by
    intro i
    exact chosenBatch_admissible (vertexIndex.symm i)
  rcases Lax60.BatchReassignment.reassignment schedule hallAdmissible with
    ⟨hpositive, hnoclash, hwidth⟩
  unfold positiveNCTD
  apply Nat.sInf_le
  exact ⟨schedule.finalTeaching, hpositive, hnoclash, hwidth⟩

end Lax60Proofs.PlanarBound
