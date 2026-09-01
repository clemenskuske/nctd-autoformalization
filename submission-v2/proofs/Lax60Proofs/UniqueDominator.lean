import Mathlib.Tactic.FinCases
import Lax60.DominatorDefinitions
import Lax60.PlanarGraphs

namespace Lax60Proofs.UniqueDominator

open Lax60.DominatorDefinitions
open Lax60.PlanarGraphs
open Lax60.TeachingMaps

universe u v

private theorem walkInterior_toWalk_eq_empty
    {V : Type u} {G : SimpleGraph V} {a b : V} (h : G.Adj a b) :
    walkInterior h.toWalk = ∅ := by
  ext x
  simp only [walkInterior, SimpleGraph.Adj.toWalk,
    SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
    List.mem_cons, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false]
  aesop

private def directTopologicalModel
    {W : Type u} {V : Type v} {H : SimpleGraph W} {G : SimpleGraph V}
    (f : H →g G) (hf : Function.Injective f) :
    TopologicalModel H G where
  branch := ⟨f, hf⟩
  route h := (f.map_rel h).toWalk
  route_isPath h := SimpleGraph.Walk.IsPath.of_adj (f.map_rel h)
  branch_avoids_interiors h _ := by
    rw [walkInterior_toWalk_eq_empty]
    simp
  route_interiors_disjoint hab hcd _ := by
    rw [walkInterior_toWalk_eq_empty, walkInterior_toWalk_eq_empty]
    simp

private theorem false_of_k33_configuration
    {V : Type u} {G : SimpleGraph V} (hplanar : IsPlanar G)
    (f : (Fin 3 ⊕ Fin 3) → V) (hf : Function.Injective f)
    (hadj : ∀ i j : Fin 3, G.Adj (f (Sum.inl i)) (f (Sum.inr j))) :
    False := by
  apply hplanar.2
  let hom :
      completeBipartiteGraph (Fin 3) (Fin 3) →g G :=
    { toFun := f
      map_rel' := by
        intro a b hab
        rcases a with i | i <;> rcases b with j | j
        · simp at hab
        · exact hadj i j
        · exact (hadj j i).symm
        · simp at hab }
  exact ⟨directTopologicalModel hom hf⟩

/--
Choose a label of the dominator outside the center ball.  Only two concepts
in the center ball can also contain that label, since three would form a
direct `K₃,₃` together with the center, the outside label, and the
dominator.  One further positive label handles each of those exceptions.
-/
theorem exists_unique_dominator_set {V : Type u}
    (G : SimpleGraph V) (hplanar : IsPlanar G)
    (v w : V)
    (hunique : dominatorSet G v = {w})
    (hactive : IsActiveDominator G v w) :
    ∃ S : Finset V, IsDominatorTeachingSet G v w S := by
  classical

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

  have hwdata : G.Adj v w ∧ Dominates G 1 v w := by
    exact hactive.1
  have hvw : G.Adj v w := hwdata.1
  have hdominates :
      closedBall G 1 v ⊆ closedBall G 1 w :=
    hwdata.2
  have hdistinct : DistinctConcepts G 1 v w := hactive.2

  have hnreverse :
      ¬ closedBall G 1 w ⊆ closedBall G 1 v := by
    intro hreverse
    apply hdistinct
    exact Set.Subset.antisymm hdominates hreverse
  obtain ⟨q, hqw, hqv⟩ := Set.not_subset.mp hnreverse

  let Bad : V → Prop := fun z =>
    z ∈ closedBall G 1 v ∧
    DistinctConcepts G 1 w z ∧
    q ∈ closedBall G 1 z

  have bad_adj_v (z : V) (hz : Bad z) : G.Adj v z := by
    rcases (ball_one_iff v z).1 hz.1 with hzv | hvz
    · subst z
      exact False.elim (hqv hz.2.2)
    · exact hvz

  have bad_adj_q (z : V) (hz : Bad z) : G.Adj q z := by
    rcases (ball_one_iff z q).1 hz.2.2 with hqz | hzq
    · subst z
      exact False.elim (hqv hz.1)
    · exact hzq.symm

  have bad_adj_w (z : V) (hz : Bad z) : G.Adj w z := by
    rcases (ball_one_iff w z).1 (hdominates hz.1) with hzw | hwz
    · subst z
      exact False.elim (hz.2.1 rfl)
    · exact hwz

  have witness_for_bad (z : V) (hz : Bad z) :
      ∃ x : V, x ∈ closedBall G 1 w ∧ x ∉ closedBall G 1 z := by
    have hz_not_dominates : ¬ Dominates G 1 v z := by
      intro hzdom
      have hzmem : z ∈ dominatorSet G v :=
        ⟨bad_adj_v z hz, hzdom⟩
      rw [hunique] at hzmem
      have hzw : z = w := by simpa using hzmem
      subst z
      exact hz.2.1 rfl
    obtain ⟨x, hxv, hxz⟩ := Set.not_subset.mp hz_not_dominates
    exact ⟨x, hdominates hxv, hxz⟩

  have hvq : v ≠ q := by
    intro hvq
    subst q
    exact hqv (hself v)
  have hqw_ne : q ≠ w := by
    intro hqw_eq
    subst q
    exact hqv ((ball_one_iff v w).2 (Or.inr hvw))

  have no_three_bad (z₁ z₂ z₃ : V)
      (hz₁ : Bad z₁) (hz₂ : Bad z₂) (hz₃ : Bad z₃)
      (h₁₂ : z₁ ≠ z₂) (h₁₃ : z₁ ≠ z₃) (h₂₃ : z₂ ≠ z₃) :
      False := by
    have hvz₁ := bad_adj_v z₁ hz₁
    have hvz₂ := bad_adj_v z₂ hz₂
    have hvz₃ := bad_adj_v z₃ hz₃
    have hqz₁ := bad_adj_q z₁ hz₁
    have hqz₂ := bad_adj_q z₂ hz₂
    have hqz₃ := bad_adj_q z₃ hz₃
    have hwz₁ := bad_adj_w z₁ hz₁
    have hwz₂ := bad_adj_w z₂ hz₂
    have hwz₃ := bad_adj_w z₃ hz₃
    have hvz₁_ne := hvz₁.ne
    have hvz₂_ne := hvz₂.ne
    have hvz₃_ne := hvz₃.ne
    have hqz₁_ne := hqz₁.ne
    have hqz₂_ne := hqz₂.ne
    have hqz₃_ne := hqz₃.ne
    have hwz₁_ne := hwz₁.ne
    have hwz₂_ne := hwz₂.ne
    have hwz₃_ne := hwz₃.ne
    let f : (Fin 3 ⊕ Fin 3) → V
      | Sum.inl i => ![v, q, w] i
      | Sum.inr j => ![z₁, z₂, z₃] j
    apply false_of_k33_configuration hplanar f
    · intro a b hab
      rcases a with i | i <;> rcases b with j | j
      all_goals
        fin_cases i <;> fin_cases j <;>
          simp_all [f]
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [f] <;> assumption

  have card_pair (a b : V) : ({a, b} : Finset V).card ≤ 2 := by
    calc
      ({a, b} : Finset V).card ≤ ({b} : Finset V).card + 1 :=
        Finset.card_insert_le a {b}
      _ = 2 := by simp

  have card_triple (a b c : V) :
      ({a, b, c} : Finset V).card ≤ 3 := by
    calc
      ({a, b, c} : Finset V).card ≤ ({b, c} : Finset V).card + 1 :=
        Finset.card_insert_le a {b, c}
      _ ≤ 2 + 1 := Nat.add_le_add_right (card_pair b c) 1
      _ = 3 := rfl

  have card_quadruple (a b c d : V) :
      ({a, b, c, d} : Finset V).card ≤ 4 := by
    calc
      ({a, b, c, d} : Finset V).card ≤
          ({b, c, d} : Finset V).card + 1 :=
        Finset.card_insert_le a {b, c, d}
      _ ≤ 3 + 1 := Nat.add_le_add_right (card_triple b c d) 1
      _ = 4 := rfl

  by_cases hexception₁ : ∃ z : V, Bad z
  · obtain ⟨z₁, hz₁⟩ := hexception₁
    obtain ⟨x₁, hx₁w, hx₁z₁⟩ := witness_for_bad z₁ hz₁
    by_cases hexception₂ : ∃ z : V, Bad z ∧ z ≠ z₁
    · obtain ⟨z₂, hz₂, hz₂z₁⟩ := hexception₂
      obtain ⟨x₂, hx₂w, hx₂z₂⟩ := witness_for_bad z₂ hz₂
      have classify (z : V) (hz : Bad z) : z = z₁ ∨ z = z₂ := by
        by_contra hnot
        have hnot₁ : z ≠ z₁ := fun h => hnot (Or.inl h)
        have hnot₂ : z ≠ z₂ := fun h => hnot (Or.inr h)
        exact no_three_bad z₁ z₂ z hz₁ hz₂ hz
          hz₂z₁.symm hnot₁.symm hnot₂.symm
      refine ⟨{v, q, x₁, x₂}, ?_⟩
      refine ⟨card_quadruple v q x₁ x₂, by simp, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx | hx | hx
        · subst x
          exact hdominates (hself v)
        · subst x
          exact hqw
        · subst x
          exact hx₁w
        · subst x
          exact hx₂w
      · intro z hz hdist _
        by_cases hqz : q ∈ closedBall G 1 z
        · rcases classify z ⟨hz, hdist, hqz⟩ with rfl | rfl
          · exact ⟨x₁, by simp, hx₁z₁⟩
          · exact ⟨x₂, by simp, hx₂z₂⟩
        · exact ⟨q, by simp, hqz⟩
    · have classify (z : V) (hz : Bad z) : z = z₁ := by
        by_contra hne
        exact hexception₂ ⟨z, hz, hne⟩
      refine ⟨{v, q, x₁}, ?_⟩
      refine
        ⟨(card_triple v q x₁).trans (by omega), by simp, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx | hx
        · subst x
          exact hdominates (hself v)
        · subst x
          exact hqw
        · subst x
          exact hx₁w
      · intro z hz hdist _
        by_cases hqz : q ∈ closedBall G 1 z
        · have hz₁eq := classify z ⟨hz, hdist, hqz⟩
          subst z
          exact ⟨x₁, by simp, hx₁z₁⟩
        · exact ⟨q, by simp, hqz⟩
  · refine ⟨{v, q}, ?_⟩
    refine ⟨(card_pair v q).trans (by omega), by simp, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · subst x
        exact hdominates (hself v)
      · subst x
        exact hqw
    · intro z hz hdist _
      have hqz : q ∉ closedBall G 1 z := by
        intro hqz
        exact hexception₁ ⟨z, hz, hdist, hqz⟩
      exact ⟨q, by simp, hqz⟩

end Lax60Proofs.UniqueDominator
