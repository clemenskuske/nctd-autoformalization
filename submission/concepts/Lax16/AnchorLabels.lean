import Lax16.TeachingMaps

/-!
---
title: An anchor label certifies against every concept that omits it
type: theorem
---
If a radius-one teaching set contains an anchor label `v`, it certifies its
concept against every closed neighborhood that omits `v`.  This is the
anchor-label observation used for every local batch in the draft.
-/

namespace Lax16.AnchorLabels

open Lax16.TeachingMaps

universe u

/-- An anchor certifies against every concept omitting that label. -/
axiom anchor_certifies {V : Type u} {G : SimpleGraph V}
    {T : TeachingMap V 1} {v w : V} (hv : v ∈ T w) :
    ∀ x : V, v ∉ closedBall G 1 x →
      ∃ y ∈ T w, y ∉ closedBall G 1 x

end Lax16.AnchorLabels
