import Lax16.BatchFramework

/-!
---
title: Last assignments from admissible batches form a global teaching map
type: theorem
---
If every batch in a finite covering schedule is admissible with width `d`,
then retaining the last assignment of each vertex produces a positive
radius-one no-clash teaching map of the same width.
-/

namespace Lax16.BatchReassignment

open Lax16.BatchFramework
open Lax16.TeachingMaps

universe u

/-- Admissibility is preserved by the last-assignment construction. -/
axiom reassignment {V : Type u} {G : SimpleGraph V} {d : ℕ}
    (S : BatchSchedule G)
    (hadmissible : ∀ i : Fin S.batchCount, IsAdmissible G d (S.batch i)) :
    IsPositive G 1 S.finalTeaching ∧
    IsNoClash G 1 S.finalTeaching ∧
    HasWidthAtMost S.finalTeaching d

end Lax16.BatchReassignment
