import Lax60.TeachingMaps

/-!
---
title: Admissible batches and last-assignment schedules
type: definition
---
This framework is defined only for positive teaching sets.  A batch consists
of a finite set of vertices and a proposed positive teaching set for each
vertex.  It is admissible at radius one when the teaching sets are uniformly
bounded, separate every pair inside the batch, and each batch vertex certifies
itself against every distinct concept outside the batch.

A finite schedule records, for each vertex, the last batch containing it.
Retaining the corresponding teaching sets defines its final assignment.
-/

namespace Lax60.BatchFramework

open Lax60.TeachingMaps

universe u

/-- A finite batch of vertices together with proposed positive teaching sets. -/
structure BatchAssignment {V : Type u} (G : SimpleGraph V) where
  /-- The vertices assigned in this batch. -/
  vertices : Finset V
  /-- A total map whose values on `vertices` are the proposed positive assignments. -/
  teaching : TeachingMap V 1

/-- The positive-teaching-set admissibility conditions from the batch construction. -/
def IsAdmissible {V : Type u} (G : SimpleGraph V) (d : ℕ)
    (B : BatchAssignment G) : Prop :=
  (∀ ⦃v x : V⦄, v ∈ B.vertices → x ∈ B.teaching v →
    x ∈ closedBall G 1 v) ∧
  (∀ v : V, v ∈ B.vertices → (B.teaching v).card ≤ d) ∧
  (∀ ⦃v w : V⦄, v ∈ B.vertices → w ∈ B.vertices →
    DistinctConcepts G 1 v w → Separates G 1 B.teaching v w) ∧
  (∀ ⦃v x : V⦄, v ∈ B.vertices → x ∉ B.vertices →
    DistinctConcepts G 1 v x →
      ∃ y ∈ B.teaching v, y ∉ closedBall G 1 x)

/--
A finite positive-teaching-set batch schedule with an explicit, verified last
batch for each vertex.  Carrying the last index as data keeps the final
assignment readable.
-/
structure BatchSchedule {V : Type u} (G : SimpleGraph V) where
  /-- Number of batches in the schedule. -/
  batchCount : ℕ
  /-- The batches, in chronological order. -/
  batch : Fin batchCount → BatchAssignment G
  /-- The last batch containing each vertex. -/
  last : V → Fin batchCount
  /-- Every vertex belongs to its selected last batch. -/
  mem_last : ∀ v : V, v ∈ (batch (last v)).vertices
  /-- No later batch contains the vertex. -/
  last_is_last :
    ∀ (v : V) (i : Fin batchCount), v ∈ (batch i).vertices → i ≤ last v

/-- The final map obtained by retaining each vertex's last positive assignment. -/
def BatchSchedule.finalTeaching {V : Type u} {G : SimpleGraph V}
    (S : BatchSchedule G) : TeachingMap V 1 :=
  fun v => (S.batch (S.last v)).teaching v

end Lax60.BatchFramework
