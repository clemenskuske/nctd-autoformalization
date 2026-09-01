import Lax60.AnchorLabels

namespace Lax60Proofs.AnchorLabels

open Lax60.TeachingMaps

universe u

/--
---
conclusion: Lax60.AnchorLabels.anchor_certifies
---
The anchor itself is the required label: it belongs to the teaching set by
hypothesis and is absent from the competing closed ball.
-/
theorem anchor_certifies {V : Type u} {G : SimpleGraph V}
    {T : TeachingMap V 1} {v w : V} (hv : v ∈ T w) :
    ∀ x : V, v ∉ closedBall G 1 x →
      ∃ y ∈ T w, y ∉ closedBall G 1 x := by
  intro x hx
  exact ⟨v, hv, hx⟩

end Lax60Proofs.AnchorLabels
