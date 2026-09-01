import Lax60.TeachingMaps

namespace Lax60Proofs.PositiveSeparation

open Lax60.TeachingMaps

universe u

/--
A separating label must belong to the teaching set whose ball contains it:
the other two cases contradict positivity.  Conversely, either
cross-containment failure supplies a separating witness.
-/
theorem positive_separation_iff {V : Type u} {G : SimpleGraph V}
    {T : TeachingMap V 1} (hT : IsPositive G 1 T) {v w : V} :
    Separates G 1 T v w ↔
      (∃ x ∈ T v, x ∉ closedBall G 1 w) ∨
      (∃ x ∈ T w, x ∉ closedBall G 1 v) := by
  unfold IsPositive at hT
  unfold Separates IsWitness
  constructor
  · rintro ⟨x, hxv | hxw, hxvw | hxwv⟩
    · exact Or.inl ⟨x, hxv, hxvw.2⟩
    · exact (hxwv.2 (hT hxv)).elim
    · exact (hxvw.2 (hT hxw)).elim
    · exact Or.inr ⟨x, hxw, hxwv.2⟩
  · rintro (⟨x, hxv, hxw⟩ | ⟨x, hxw, hxv⟩)
    · exact ⟨x, Or.inl hxv, Or.inl ⟨hT hxv, hxw⟩⟩
    · exact ⟨x, Or.inr hxw, Or.inr ⟨hT hxw, hxv⟩⟩

end Lax60Proofs.PositiveSeparation
