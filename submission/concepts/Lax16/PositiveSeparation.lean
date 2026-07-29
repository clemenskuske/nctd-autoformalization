import Lax16.TeachingMaps

/-!
---
title: Positive separation as cross-containment failure
type: theorem
---
For a positive radius-one teaching map, two vertices are separated exactly
when the teaching set of one contains a label outside the closed radius-one
ball of the other.  This is the containment reformulation used throughout
the draft.
-/

namespace Lax16.PositiveSeparation

open Lax16.TeachingMaps

universe u

/-- Positive separation is equivalent to one of the two cross-containment failures. -/
axiom positive_separation_iff {V : Type u} {G : SimpleGraph V}
    {T : TeachingMap V 1} (hT : IsPositive G 1 T) {v w : V} :
    Separates G 1 T v w ↔
      (∃ x ∈ T v, x ∉ closedBall G 1 w) ∨
      (∃ x ∈ T w, x ∉ closedBall G 1 v)

end Lax16.PositiveSeparation
