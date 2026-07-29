import Lax16.TeachingMaps

/-!
---
title: Copying a teaching set across closed-ball twins
type: theorem
---
If two vertices have the same closed neighborhood, they represent the same
radius-one concept and have interchangeable label behavior across all such
concepts.  Replacing the teaching set of one twin by a copy of the other's
preserves positivity, the no-clash property, the width bound, and nonemptiness.
-/

namespace Lax16.TwinReduction

open Lax16.TeachingMaps

universe u

/-- Replace the teaching set at `target` by the set at `source`. -/
noncomputable def copyTeachingSet {V : Type u} {k : ℕ} (T : TeachingMap V k)
    (source target : V) : TeachingMap V k := by
  classical
  exact fun v => if v = target then T source else T v

/-- Copying a teaching set between radius-one twins preserves validity. -/
axiom copy_twin_preserves {V : Type u} {G : SimpleGraph V} {d : ℕ}
    {T : TeachingMap V 1} {source target : V}
    (htwins : closedBall G 1 source = closedBall G 1 target)
    (hpositive : IsPositive G 1 T)
    (hnoclash : IsNoClash G 1 T)
    (hwidth : HasWidthAtMost T d)
    (hnonempty : HasNonemptySets T) :
    IsPositive G 1 (copyTeachingSet T source target) ∧
    IsNoClash G 1 (copyTeachingSet T source target) ∧
    HasWidthAtMost (copyTeachingSet T source target) d ∧
    HasNonemptySets (copyTeachingSet T source target)

end Lax16.TwinReduction
