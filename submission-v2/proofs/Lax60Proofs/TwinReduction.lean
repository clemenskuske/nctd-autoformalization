import Lax60.TeachingMaps

namespace Lax60Proofs.TwinReduction

open Lax60.TeachingMaps

universe u

/--
For a pair involving the target twin, apply the original no-clash condition
to the corresponding pair involving the source twin.  Equality of their
closed balls transfers both the distinctness hypothesis and the witness.
-/
lemma copy_twin_preserves {V : Type u} {G : SimpleGraph V} {d : ℕ}
    {T : TeachingMap V 1} {source target : V}
    (htwins : closedBall G 1 source = closedBall G 1 target)
    (hpositive : IsPositive G 1 T)
    (hnoclash : IsNoClash G 1 T)
    (hwidth : HasWidthAtMost T d)
    (hnonempty : HasNonemptySets T) :
    IsPositive G 1 (copyTeachingSet T source target) ∧
    IsNoClash G 1 (copyTeachingSet T source target) ∧
    HasWidthAtMost (copyTeachingSet T source target) d ∧
    HasNonemptySets (copyTeachingSet T source target) := by
  classical
  constructor
  · intro v x hx
    by_cases hv : v = target
    · subst v
      have hxsource : x ∈ T source := by
        simpa [copyTeachingSet] using hx
      have hxball : x ∈ closedBall G 1 source := hpositive hxsource
      simpa [htwins] using hxball
    · apply hpositive
      simpa [copyTeachingSet, hv] using hx
  constructor
  · intro v w hdifferent
    by_cases hv : v = target
    · subst v
      by_cases hw : w = target
      · subst w
        exact (hdifferent rfl).elim
      · have hdifferent' : DistinctConcepts G 1 source w := by
          intro hequal
          apply hdifferent
          exact htwins.symm.trans hequal
        rcases hnoclash hdifferent' with ⟨x, hxsets, hxwitness⟩
        refine ⟨x, ?_, ?_⟩
        · simpa [copyTeachingSet, hw] using hxsets
        · simpa [IsWitness, htwins] using hxwitness
    · by_cases hw : w = target
      · subst w
        have hdifferent' : DistinctConcepts G 1 v source := by
          intro hequal
          apply hdifferent
          exact hequal.trans htwins
        rcases hnoclash hdifferent' with ⟨x, hxsets, hxwitness⟩
        refine ⟨x, ?_, ?_⟩
        · simpa [copyTeachingSet, hv] using hxsets
        · simpa [IsWitness, htwins] using hxwitness
      · rcases hnoclash hdifferent with ⟨x, hxsets, hxwitness⟩
        refine ⟨x, ?_, hxwitness⟩
        simpa [copyTeachingSet, hv, hw] using hxsets
  constructor
  · intro v
    by_cases hv : v = target
    · subst v
      simpa [copyTeachingSet] using hwidth source
    · simpa [copyTeachingSet, hv] using hwidth v
  · intro v
    by_cases hv : v = target
    · subst v
      simpa [copyTeachingSet] using hnonempty source
    · simpa [copyTeachingSet, hv] using hnonempty v

end Lax60Proofs.TwinReduction
