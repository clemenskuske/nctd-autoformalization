import Lax16Proofs.DominatorCount
import Lax16Proofs.UniqueDominator
import Lax16Proofs.TwoDominators

namespace Lax16Proofs.DominatorCompletion

open Lax16.DominatorDefinitions
open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u

/--
The planar counting bound leaves no dominators, one dominator, or (only at
degree four) two dominators.  The empty case is vacuous, the singleton case
uses the unique-dominator construction when that vertex is active, and the
two-element case uses the simultaneous degree-four construction.
-/
lemma exists_dominator_completion {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hplanar : IsPlanar G)
    (v : V) (hdegree : 4 ≤ (G.neighborSet v).ncard) :
    ∃ T : TeachingMap V 1, CompletesActiveDominators G v T := by
  classical

  have empty_completion (hempty : dominatorSet G v = ∅) :
      ∃ T : TeachingMap V 1, CompletesActiveDominators G v T := by
    refine ⟨fun _ => ∅, ?_⟩
    constructor
    · intro w hactive
      have hw : w ∈ dominatorSet G v := hactive.1
      rw [hempty] at hw
      simp at hw
    · intro w _ hactive _ _
      have hw : w ∈ dominatorSet G v := hactive.1
      rw [hempty] at hw
      simp at hw

  have singleton_completion (w : V)
      (hsingleton : dominatorSet G v = {w}) :
      ∃ T : TeachingMap V 1, CompletesActiveDominators G v T := by
    by_cases hactive : IsActiveDominator G v w
    · obtain ⟨S, hS⟩ :=
        Lax16Proofs.UniqueDominator.exists_unique_dominator_set
          G hplanar v w hsingleton hactive
      refine ⟨fun x => if x = w then S else ∅, ?_⟩
      constructor
      · intro x hx
        have hxw : x = w := by
          have hxmem : x ∈ dominatorSet G v := hx.1
          rw [hsingleton] at hxmem
          simpa using hxmem
        subst x
        simpa using hS
      · intro x y hx hy hxy
        have hxw : x = w := by
          have hxmem : x ∈ dominatorSet G v := hx.1
          rw [hsingleton] at hxmem
          simpa using hxmem
        have hyw : y = w := by
          have hymem : y ∈ dominatorSet G v := hy.1
          rw [hsingleton] at hymem
          simpa using hymem
        subst x
        subst y
        exact (hxy rfl).elim
    · refine ⟨fun _ => ∅, ?_⟩
      constructor
      · intro x hx
        have hxw : x = w := by
          have hxmem : x ∈ dominatorSet G v := hx.1
          rw [hsingleton] at hxmem
          simpa using hxmem
        subst x
        exact False.elim (hactive hx)
      · intro x _ hx _ _
        have hxw : x = w := by
          have hxmem : x ∈ dominatorSet G v := hx.1
          rw [hsingleton] at hxmem
          simpa using hxmem
        subst x
        exact False.elim (hactive hx)

  have hbounds :=
    Lax16Proofs.DominatorCount.dominator_count_bounds G hplanar v
  by_cases hdegree_four : (G.neighborSet v).ncard = 4
  · have hcard_le : (dominatorSet G v).ncard ≤ 2 :=
      hbounds.2 hdegree_four
    have hcard_cases :
        (dominatorSet G v).ncard = 0 ∨
        (dominatorSet G v).ncard = 1 ∨
        (dominatorSet G v).ncard = 2 := by
      omega
    rcases hcard_cases with hzero | hone | htwo
    · apply empty_completion
      exact
        (Set.ncard_eq_zero (Set.toFinite (dominatorSet G v))).mp hzero
    · obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hone
      exact singleton_completion w hw
    · obtain ⟨w₁, w₂, hne, hdom⟩ := Set.ncard_eq_two.mp htwo
      exact
        Lax16Proofs.TwoDominators.exists_two_dominator_assignment
          G hplanar v w₁ w₂ hdegree_four hne hdom
  · have hdegree_five : 5 ≤ (G.neighborSet v).ncard := by omega
    have hcard_le : (dominatorSet G v).ncard ≤ 1 :=
      hbounds.1 hdegree_five
    have hcard_cases :
        (dominatorSet G v).ncard = 0 ∨
        (dominatorSet G v).ncard = 1 := by
      omega
    rcases hcard_cases with hzero | hone
    · apply empty_completion
      exact
        (Set.ncard_eq_zero (Set.toFinite (dominatorSet G v))).mp hzero
    · obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hone
      exact singleton_completion w hw

end Lax16Proofs.DominatorCompletion
