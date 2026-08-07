import Mathlib.Combinatorics.SimpleGraph.Finite
import Lax16.DominatorDefinitions
import Lax16.PlanarGraphs

namespace Lax16Proofs.TwoDominators

open Lax16.DominatorDefinitions
open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u

/--
The two neighbors outside the dominating pair are nonadjacent, so they
witness the two remaining internal comparisons.  Each active dominator also
receives an outside witness.  When both dominators are active and distinct,
one outside witness is chosen from their symmetric difference, allowing the
pair to be separated from whichever side supplies that witness.
-/
theorem exists_two_dominator_assignment {V : Type u} [Fintype V]
    (G : SimpleGraph V) (_hplanar : IsPlanar G)
    (v w₁ w₂ : V)
    (hdegree : (G.neighborSet v).ncard = 4)
    (hne : w₁ ≠ w₂)
    (hdom : dominatorSet G v = {w₁, w₂}) :
    ∃ T : TeachingMap V 1, CompletesActiveDominators G v T := by
  classical
  letI : Fintype (G.neighborSet v) := Fintype.ofFinite _

  have ball_one_iff (a b : V) :
      b ∈ closedBall G 1 a ↔ b = a ∨ G.Adj a b := by
    constructor
    · rintro ⟨p, hp⟩
      have hlength : p.length = 0 ∨ p.length = 1 := by omega
      rcases hlength with hzero | hone
      · exact Or.inl (p.eq_of_length_eq_zero hzero).symm
      · exact Or.inr (p.adj_of_length_eq_one hone)
    · rintro (rfl | hab)
      · exact ⟨SimpleGraph.Walk.nil, by simp⟩
      · exact ⟨hab.toWalk, by simp⟩

  have hself (a : V) : a ∈ closedBall G 1 a :=
    (ball_one_iff a a).2 (Or.inl rfl)

  have hw₁mem : w₁ ∈ dominatorSet G v := by
    rw [hdom]
    simp
  have hw₂mem : w₂ ∈ dominatorSet G v := by
    rw [hdom]
    simp
  have hw₁data : G.Adj v w₁ ∧ Dominates G 1 v w₁ := hw₁mem
  have hw₂data : G.Adj v w₂ ∧ Dominates G 1 v w₂ := hw₂mem
  have hvw₁ := hw₁data.1
  have hvw₂ := hw₂data.1
  have hw₁dominates :
      closedBall G 1 v ⊆ closedBall G 1 w₁ := hw₁data.2
  have hw₂dominates :
      closedBall G 1 v ⊆ closedBall G 1 w₂ := hw₂data.2

  let N := G.neighborFinset v
  have hNcard : N.card = 4 := by
    simpa [N, SimpleGraph.neighborFinset_def] using hdegree
  have hw₁N : w₁ ∈ N := by
    exact (G.mem_neighborFinset v w₁).2 hvw₁
  have hw₂N : w₂ ∈ N := by
    exact (G.mem_neighborFinset v w₂).2 hvw₂
  have hpair_subset : ({w₁, w₂} : Finset V) ⊆ N := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hw₁N
    · exact hw₂N
  have hpair_card : ({w₁, w₂} : Finset V).card = 2 := by
    simp [hne]
  have hremaining_card :
      (N \ ({w₁, w₂} : Finset V)).card = 2 := by
    rw [Finset.card_sdiff_of_subset hpair_subset, hNcard, hpair_card]
  obtain ⟨x₁, x₂, hx₁x₂, hremaining⟩ :=
    Finset.card_eq_two.mp hremaining_card
  have hx₁remaining : x₁ ∈ N \ ({w₁, w₂} : Finset V) := by
    rw [hremaining]
    simp
  have hx₂remaining : x₂ ∈ N \ ({w₁, w₂} : Finset V) := by
    rw [hremaining]
    simp
  have hx₁N : x₁ ∈ N := (Finset.mem_sdiff.mp hx₁remaining).1
  have hx₂N : x₂ ∈ N := (Finset.mem_sdiff.mp hx₂remaining).1
  have hx₁notpair : x₁ ∉ ({w₁, w₂} : Finset V) :=
    (Finset.mem_sdiff.mp hx₁remaining).2
  have hx₂notpair : x₂ ∉ ({w₁, w₂} : Finset V) :=
    (Finset.mem_sdiff.mp hx₂remaining).2
  have hx₁w₁ : x₁ ≠ w₁ := by
    intro h
    subst x₁
    exact hx₁notpair (by simp)
  have hx₁w₂ : x₁ ≠ w₂ := by
    intro h
    subst x₁
    exact hx₁notpair (by simp)
  have hx₂w₁ : x₂ ≠ w₁ := by
    intro h
    subst x₂
    exact hx₂notpair (by simp)
  have hx₂w₂ : x₂ ≠ w₂ := by
    intro h
    subst x₂
    exact hx₂notpair (by simp)
  have hvx₁ : G.Adj v x₁ := (G.mem_neighborFinset v x₁).1 hx₁N
  have hvx₂ : G.Adj v x₂ := (G.mem_neighborFinset v x₂).1 hx₂N
  have hx₁ballv : x₁ ∈ closedBall G 1 v :=
    (ball_one_iff v x₁).2 (Or.inr hvx₁)
  have hx₂ballv : x₂ ∈ closedBall G 1 v :=
    (ball_one_iff v x₂).2 (Or.inr hvx₂)

  have classify_neighbor (z : V) (hz : G.Adj v z) :
      z = w₁ ∨ z = w₂ ∨ z = x₁ ∨ z = x₂ := by
    have hzN : z ∈ N := (G.mem_neighborFinset v z).2 hz
    by_cases hzpair : z ∈ ({w₁, w₂} : Finset V)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hzpair
      exact hzpair.elim Or.inl (fun h => Or.inr (Or.inl h))
    · have hzremaining : z ∈ N \ ({w₁, w₂} : Finset V) :=
        Finset.mem_sdiff.mpr ⟨hzN, hzpair⟩
      rw [hremaining] at hzremaining
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzremaining
      exact hzremaining.elim
        (fun h => Or.inr (Or.inr (Or.inl h)))
        (fun h => Or.inr (Or.inr (Or.inr h)))

  have hw₁x₁ : G.Adj w₁ x₁ := by
    rcases (ball_one_iff w₁ x₁).1 (hw₁dominates hx₁ballv) with h | h
    · exact False.elim (hx₁w₁ h)
    · exact h
  have hw₁x₂ : G.Adj w₁ x₂ := by
    rcases (ball_one_iff w₁ x₂).1 (hw₁dominates hx₂ballv) with h | h
    · exact False.elim (hx₂w₁ h)
    · exact h
  have hw₂x₁ : G.Adj w₂ x₁ := by
    rcases (ball_one_iff w₂ x₁).1 (hw₂dominates hx₁ballv) with h | h
    · exact False.elim (hx₁w₂ h)
    · exact h
  have hw₂x₂ : G.Adj w₂ x₂ := by
    rcases (ball_one_iff w₂ x₂).1 (hw₂dominates hx₂ballv) with h | h
    · exact False.elim (hx₂w₂ h)
    · exact h

  have hx₁x₂_nonadj : ¬ G.Adj x₁ x₂ := by
    intro hx₁x₂adj
    have hx₁dominates : Dominates G 1 v x₁ := by
      intro z hz
      rcases (ball_one_iff v z).1 hz with hzv | hvz
      · subst z
        exact (ball_one_iff x₁ v).2 (Or.inr hvx₁.symm)
      · rcases classify_neighbor z hvz with h | h | h | h
        · subst z
          exact (ball_one_iff x₁ w₁).2 (Or.inr hw₁x₁.symm)
        · subst z
          exact (ball_one_iff x₁ w₂).2 (Or.inr hw₂x₁.symm)
        · subst z
          exact hself x₁
        · subst z
          exact (ball_one_iff x₁ x₂).2 (Or.inr hx₁x₂adj)
    have hx₁dommem : x₁ ∈ dominatorSet G v :=
      ⟨hvx₁, hx₁dominates⟩
    rw [hdom] at hx₁dommem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx₁dommem
    exact hx₁dommem.elim hx₁w₁ hx₁w₂

  have hx₂_not_ball_x₁ : x₂ ∉ closedBall G 1 x₁ := by
    intro h
    rcases (ball_one_iff x₁ x₂).1 h with heq | hadj
    · exact hx₁x₂ heq.symm
    · exact hx₁x₂_nonadj hadj
  have hx₁_not_ball_x₂ : x₁ ∉ closedBall G 1 x₂ := by
    intro h
    rcases (ball_one_iff x₂ x₁).1 h with heq | hadj
    · exact hx₁x₂ heq
    · exact hx₁x₂_nonadj hadj.symm

  have outside_of_active (w : V) (hw : IsActiveDominator G v w) :
      ∃ q : V, q ∈ closedBall G 1 w ∧ q ∉ closedBall G 1 v := by
    have hwdata : G.Adj v w ∧ Dominates G 1 v w := hw.1
    have hnreverse :
        ¬ closedBall G 1 w ⊆ closedBall G 1 v := by
      intro hreverse
      exact hw.2 (Set.Subset.antisymm hwdata.2 hreverse)
    exact Set.not_subset.mp hnreverse

  have card_quadruple (a b c d : V) :
      ({a, b, c, d} : Finset V).card ≤ 4 := by
    calc
      ({a, b, c, d} : Finset V).card ≤
          ({b, c, d} : Finset V).card + 1 :=
        Finset.card_insert_le a {b, c, d}
      _ ≤ ({c, d} : Finset V).card + 2 := by
        have h := Finset.card_insert_le b {c, d}
        omega
      _ ≤ ({d} : Finset V).card + 3 := by
        have h := Finset.card_insert_le c {d}
        omega
      _ = 4 := by simp

  have valid_set (w q : V)
      (hw : IsActiveDominator G v w)
      (hqw : q ∈ closedBall G 1 w)
      (hqv : q ∉ closedBall G 1 v) :
      IsDominatorTeachingSet G v w {v, q, x₁, x₂} := by
    have hwdata : G.Adj v w ∧ Dominates G 1 v w := hw.1
    refine ⟨card_quadruple v q x₁ x₂, by simp, ?_, ?_⟩
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with hy | hy | hy | hy
      · subst y
        exact hwdata.2 (hself v)
      · subst y
        exact hqw
      · subst y
        exact hwdata.2 hx₁ballv
      · subst y
        exact hwdata.2 hx₂ballv
    · intro z hz hdist hznotactive
      rcases (ball_one_iff v z).1 hz with hzv | hvz
      · subst z
        exact ⟨q, by simp, hqv⟩
      · rcases classify_neighbor z hvz with h | h | h | h
        · subst z
          have hznotdistinct : ¬ DistinctConcepts G 1 v w₁ :=
            fun h => hznotactive ⟨hw₁mem, h⟩
          have hequal :
              closedBall G 1 v = closedBall G 1 w₁ := by
            exact not_ne_iff.mp hznotdistinct
          exact ⟨q, by simp, fun h => hqv (hequal ▸ h)⟩
        · subst z
          have hznotdistinct : ¬ DistinctConcepts G 1 v w₂ :=
            fun h => hznotactive ⟨hw₂mem, h⟩
          have hequal :
              closedBall G 1 v = closedBall G 1 w₂ := by
            exact not_ne_iff.mp hznotdistinct
          exact ⟨q, by simp, fun h => hqv (hequal ▸ h)⟩
        · subst z
          exact ⟨x₂, by simp, hx₂_not_ball_x₁⟩
        · subst z
          exact ⟨x₁, by simp, hx₁_not_ball_x₂⟩

  have finish (S₁ S₂ : Finset V)
      (hvalid₁ :
        IsActiveDominator G v w₁ →
          IsDominatorTeachingSet G v w₁ S₁)
      (hvalid₂ :
        IsActiveDominator G v w₂ →
          IsDominatorTeachingSet G v w₂ S₂)
      (hpair :
        IsActiveDominator G v w₁ →
        IsActiveDominator G v w₂ →
        DistinctConcepts G 1 w₁ w₂ →
          ∃ y : V, (y ∈ S₁ ∨ y ∈ S₂) ∧
            (IsWitness G 1 y w₁ w₂ ∨ IsWitness G 1 y w₂ w₁)) :
      ∃ T : TeachingMap V 1, CompletesActiveDominators G v T := by
    let T : TeachingMap V 1 := fun z =>
      if z = w₁ then S₁ else if z = w₂ then S₂ else ∅
    refine ⟨T, ?_, ?_⟩
    · intro z hz
      have hzmem : z ∈ dominatorSet G v := hz.1
      rw [hdom] at hzmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzmem
      rcases hzmem with hzw₁ | hzw₂
      · subst z
        simpa [T] using hvalid₁ hz
      · subst z
        simpa [T, hne, hne.symm] using hvalid₂ hz
    · intro a b ha hb hab
      have hamem : a ∈ dominatorSet G v := ha.1
      have hbmem : b ∈ dominatorSet G v := hb.1
      rw [hdom] at hamem hbmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hamem hbmem
      rcases hamem with haw₁ | haw₂ <;>
        rcases hbmem with hbw₁ | hbw₂
      · subst a
        subst b
        exact False.elim (hab rfl)
      · subst a
        subst b
        obtain ⟨y, hy, hwit⟩ := hpair ha hb hab
        refine ⟨y, ?_, hwit⟩
        simpa [T, hne, hne.symm] using hy
      · subst a
        subst b
        obtain ⟨y, hy, hwit⟩ := hpair hb ha (fun h => hab h.symm)
        refine ⟨y, ?_, ?_⟩
        · simpa [T, hne, hne.symm] using hy.symm
        · exact hwit.symm
      · subst a
        subst b
        exact False.elim (hab rfl)

  by_cases hactive₁ : IsActiveDominator G v w₁
  · obtain ⟨q₁, hq₁w₁, hq₁v⟩ := outside_of_active w₁ hactive₁
    by_cases hactive₂ : IsActiveDominator G v w₂
    · obtain ⟨q₂, hq₂w₂, hq₂v⟩ := outside_of_active w₂ hactive₂
      by_cases hsubset :
          closedBall G 1 w₁ ⊆ closedBall G 1 w₂
      · by_cases hequal :
            closedBall G 1 w₁ = closedBall G 1 w₂
        · apply finish {v, q₁, x₁, x₂} {v, q₂, x₁, x₂}
          · intro _
            exact valid_set w₁ q₁ hactive₁ hq₁w₁ hq₁v
          · intro _
            exact valid_set w₂ q₂ hactive₂ hq₂w₂ hq₂v
          · intro _ _ hdistinct
            exact False.elim (hdistinct hequal)
        · have hnreverse :
              ¬ closedBall G 1 w₂ ⊆ closedBall G 1 w₁ := by
            intro hreverse
            exact hequal (Set.Subset.antisymm hsubset hreverse)
          obtain ⟨q, hqw₂, hqw₁⟩ := Set.not_subset.mp hnreverse
          have hqv : q ∉ closedBall G 1 v := by
            intro h
            exact hqw₁ (hw₁dominates h)
          apply finish {v, q₁, x₁, x₂} {v, q, x₁, x₂}
          · intro _
            exact valid_set w₁ q₁ hactive₁ hq₁w₁ hq₁v
          · intro _
            exact valid_set w₂ q hactive₂ hqw₂ hqv
          · intro _ _ _
            exact ⟨q, Or.inr (by simp),
              Or.inr ⟨hqw₂, hqw₁⟩⟩
      · obtain ⟨q, hqw₁, hqw₂⟩ := Set.not_subset.mp hsubset
        have hqv : q ∉ closedBall G 1 v := by
          intro h
          exact hqw₂ (hw₂dominates h)
        apply finish {v, q, x₁, x₂} {v, q₂, x₁, x₂}
        · intro _
          exact valid_set w₁ q hactive₁ hqw₁ hqv
        · intro _
          exact valid_set w₂ q₂ hactive₂ hq₂w₂ hq₂v
        · intro _ _ _
          exact ⟨q, Or.inl (by simp),
            Or.inl ⟨hqw₁, hqw₂⟩⟩
    · apply finish {v, q₁, x₁, x₂} ∅
      · intro _
        exact valid_set w₁ q₁ hactive₁ hq₁w₁ hq₁v
      · intro h
        exact False.elim (hactive₂ h)
      · intro _ h
        exact False.elim (hactive₂ h)
  · by_cases hactive₂ : IsActiveDominator G v w₂
    · obtain ⟨q₂, hq₂w₂, hq₂v⟩ := outside_of_active w₂ hactive₂
      apply finish ∅ {v, q₂, x₁, x₂}
      · intro h
        exact False.elim (hactive₁ h)
      · intro _
        exact valid_set w₂ q₂ hactive₂ hq₂w₂ hq₂v
      · intro h
        exact False.elim (hactive₁ h)
    · apply finish ∅ ∅
      · intro h
        exact False.elim (hactive₁ h)
      · intro h
        exact False.elim (hactive₂ h)
      · intro h
        exact False.elim (hactive₁ h)

end Lax16Proofs.TwoDominators
