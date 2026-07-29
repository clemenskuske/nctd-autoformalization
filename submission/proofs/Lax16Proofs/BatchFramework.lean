import Lax16.BatchFramework

namespace Lax16Proofs.BatchFramework

open Lax16.TeachingMaps
open Lax16.BatchFramework

universe u

/--
---
conclusion: Lax16.BatchFramework.reassignment
---
Positivity and width pass directly from each vertex's last batch.  For a
pair of vertices, their last batches either agree, when within-batch
separation applies, or one is later.  In the latter case the earlier vertex
cannot occur in the later batch, so the later vertex's outside-batch
certificate separates the final assignments.
-/
theorem reassignment {V : Type u} {G : SimpleGraph V} {d : ℕ}
    (S : BatchSchedule G)
    (hadmissible : ∀ i : Fin S.batchCount, IsAdmissible G d (S.batch i)) :
    IsPositive G 1 S.finalTeaching ∧
    IsNoClash G 1 S.finalTeaching ∧
    HasWidthAtMost S.finalTeaching d := by
  unfold IsAdmissible at hadmissible
  constructor
  · intro v x hx
    change x ∈ (S.batch (S.last v)).teaching v at hx
    exact (hadmissible (S.last v)).1 (S.mem_last v) hx
  constructor
  · intro v w hvw
    unfold Separates
    rcases lt_trichotomy (S.last v) (S.last w) with hlast | hlast | hlast
    · have hv_not_mem : v ∉ (S.batch (S.last w)).vertices := by
        intro hv_mem
        exact (not_le_of_gt hlast) (S.last_is_last v (S.last w) hv_mem)
      have hwv : DistinctConcepts G 1 w v := Ne.symm hvw
      rcases (hadmissible (S.last w)).2.2.2
          (S.mem_last w) hv_not_mem hwv with ⟨x, hxT, hxv⟩
      have hxw : x ∈ closedBall G 1 w :=
        (hadmissible (S.last w)).1 (S.mem_last w) hxT
      refine ⟨x, Or.inr ?_, Or.inr ⟨hxw, hxv⟩⟩
      change x ∈ (S.batch (S.last w)).teaching w
      exact hxT
    · have hw_mem : w ∈ (S.batch (S.last v)).vertices := by
        rw [hlast]
        exact S.mem_last w
      have hsep := (hadmissible (S.last v)).2.2.1
        (S.mem_last v) hw_mem hvw
      unfold Separates at hsep
      rcases hsep with ⟨x, hxv | hxw, hxWitness⟩
      · refine ⟨x, Or.inl ?_, hxWitness⟩
        change x ∈ (S.batch (S.last v)).teaching v
        exact hxv
      · refine ⟨x, Or.inr ?_, hxWitness⟩
        change x ∈ (S.batch (S.last w)).teaching w
        simpa only [hlast] using hxw
    · have hw_not_mem : w ∉ (S.batch (S.last v)).vertices := by
        intro hw_mem
        exact (not_le_of_gt hlast) (S.last_is_last w (S.last v) hw_mem)
      rcases (hadmissible (S.last v)).2.2.2
          (S.mem_last v) hw_not_mem hvw with ⟨x, hxT, hxw⟩
      have hxv : x ∈ closedBall G 1 v :=
        (hadmissible (S.last v)).1 (S.mem_last v) hxT
      refine ⟨x, Or.inl ?_, Or.inl ⟨hxv, hxw⟩⟩
      change x ∈ (S.batch (S.last v)).teaching v
      exact hxT
  · intro v
    change ((S.batch (S.last v)).teaching v).card ≤ d
    exact (hadmissible (S.last v)).2.1 v (S.mem_last v)

end Lax16Proofs.BatchFramework
