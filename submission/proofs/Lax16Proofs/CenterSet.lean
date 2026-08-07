import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases
import Lax16.DominatorDefinitions
import Lax16.PlanarGraphs

namespace Lax16Proofs.CenterSet

open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u v

set_option maxHeartbeats 2000000

private theorem walkInterior_toWalk_eq_empty
    {V : Type u} {G : SimpleGraph V} {a b : V} (h : G.Adj a b) :
    walkInterior h.toWalk = ∅ := by
  ext x
  simp only [walkInterior, SimpleGraph.Adj.toWalk,
    SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
    List.mem_cons, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
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

private theorem false_of_k5_configuration
    {V : Type u} {G : SimpleGraph V} (hplanar : IsPlanar G)
    (f : Fin 5 → V) (hf : Function.Injective f)
    (hadj : ∀ i j : Fin 5, i ≠ j → G.Adj (f i) (f j)) :
    False := by
  apply hplanar.1
  let hom : (⊤ : SimpleGraph (Fin 5)) →g G :=
    { toFun := f
      map_rel' := by
        intro i j hij
        exact hadj i j (by simpa using hij) }
  exact ⟨directTopologicalModel hom hf⟩

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
Choose two nonadjacent neighbors of the center.  At most two
non-dominating neighbors contain both labels, since three would form a
direct `K₃,₃`; add one missing neighbor label for each exception and pad the
result inside the neighborhood to cardinality four.
-/
theorem exists_center_set {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hplanar : IsPlanar G)
    (v : V) (hdegree : 4 ≤ (G.neighborSet v).ncard) :
    ∃ W : Finset V,
      W.card = 4 ∧
      (∀ w ∈ W, G.Adj v w) ∧
      ∀ w : V, G.Adj v w → ¬ Dominates G 1 v w →
        ∃ x ∈ W, x ∉ closedBall G 1 w := by
  classical
  letI : Fintype (G.neighborSet v) := Fintype.ofFinite _
  have hdegree_finset : 4 ≤ (G.neighborFinset v).card := by
    simpa [SimpleGraph.neighborFinset_def] using hdegree
  have hfin_four :
      Fintype.card (Fin 4) ≤ (G.neighborFinset v).card := by
    simpa using hdegree_finset
  obtain ⟨four, hfour⟩ :=
    Function.Embedding.exists_of_card_le_finset hfin_four
  have hfour_mem (i : Fin 4) : four i ∈ G.neighborFinset v :=
    hfour ⟨i, rfl⟩
  have hfour_adj (i : Fin 4) : G.Adj v (four i) :=
    (G.mem_neighborFinset v (four i)).1 (hfour_mem i)

  have hnonadjacent :
      ∃ w₁ w₂ : V,
        w₁ ∈ G.neighborFinset v ∧
        w₂ ∈ G.neighborFinset v ∧
        w₁ ≠ w₂ ∧ ¬ G.Adj w₁ w₂ := by
    by_contra hnone
    have hall (a b : V)
        (ha : a ∈ G.neighborFinset v)
        (hb : b ∈ G.neighborFinset v)
        (hne : a ≠ b) : G.Adj a b := by
      by_contra hnab
      exact hnone ⟨a, b, ha, hb, hne, hnab⟩
    have h01 : G.Adj (four 0) (four 1) :=
      hall _ _ (hfour_mem 0) (hfour_mem 1) (four.injective.ne (by decide))
    have h02 : G.Adj (four 0) (four 2) :=
      hall _ _ (hfour_mem 0) (hfour_mem 2) (four.injective.ne (by decide))
    have h03 : G.Adj (four 0) (four 3) :=
      hall _ _ (hfour_mem 0) (hfour_mem 3) (four.injective.ne (by decide))
    have h12 : G.Adj (four 1) (four 2) :=
      hall _ _ (hfour_mem 1) (hfour_mem 2) (four.injective.ne (by decide))
    have h13 : G.Adj (four 1) (four 3) :=
      hall _ _ (hfour_mem 1) (hfour_mem 3) (four.injective.ne (by decide))
    have h23 : G.Adj (four 2) (four 3) :=
      hall _ _ (hfour_mem 2) (hfour_mem 3) (four.injective.ne (by decide))
    have hv0 : v ≠ four 0 := (hfour_adj 0).ne
    have hv1 : v ≠ four 1 := (hfour_adj 1).ne
    have hv2 : v ≠ four 2 := (hfour_adj 2).ne
    have hv3 : v ≠ four 3 := (hfour_adj 3).ne
    have h0v_ne : four 0 ≠ v := hv0.symm
    have h1v_ne : four 1 ≠ v := hv1.symm
    have h2v_ne : four 2 ≠ v := hv2.symm
    have h3v_ne : four 3 ≠ v := hv3.symm
    have h10 := h01.symm
    have h20 := h02.symm
    have h30 := h03.symm
    have h21 := h12.symm
    have h31 := h13.symm
    have h32 := h23.symm
    have h0v := (hfour_adj 0).symm
    have h1v := (hfour_adj 1).symm
    have h2v := (hfour_adj 2).symm
    have h3v := (hfour_adj 3).symm
    let f : Fin 5 → V := ![v, four 0, four 1, four 2, four 3]
    apply false_of_k5_configuration hplanar f
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [f, hv0, hv1, hv2, hv3, h0v_ne, h1v_ne, h2v_ne,
          h3v_ne] at hij ⊢
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [f, hfour_adj, h01, h02, h03, h10, h12, h13,
          h20, h21, h23, h30, h31, h32, h0v, h1v, h2v, h3v] at hij ⊢

  obtain ⟨w₁, w₂, hw₁mem, hw₂mem, hw₁w₂, hw₁w₂_nonadj⟩ :=
    hnonadjacent
  have hvw₁ : G.Adj v w₁ := (G.mem_neighborFinset v w₁).1 hw₁mem
  have hvw₂ : G.Adj v w₂ := (G.mem_neighborFinset v w₂).1 hw₂mem

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

  let Bad : V → Prop := fun z =>
    G.Adj v z ∧
    ¬ Dominates G 1 v z ∧
    w₁ ∈ closedBall G 1 z ∧
    w₂ ∈ closedBall G 1 z

  have bad_adj_w₁ (z : V) (hz : Bad z) : G.Adj w₁ z := by
    rcases (ball_one_iff z w₁).1 hz.2.2.1 with hw₁z | hzw₁
    · subst z
      rcases (ball_one_iff w₁ w₂).1 hz.2.2.2 with hw₂w₁ | hadj
      · exact False.elim (hw₁w₂ hw₂w₁.symm)
      · exact False.elim (hw₁w₂_nonadj hadj)
    · exact hzw₁.symm

  have bad_adj_w₂ (z : V) (hz : Bad z) : G.Adj w₂ z := by
    rcases (ball_one_iff z w₂).1 hz.2.2.2 with hw₂z | hzw₂
    · subst z
      rcases (ball_one_iff w₂ w₁).1 hz.2.2.1 with hw₁w₂' | hadj
      · exact False.elim (hw₁w₂ hw₁w₂')
      · exact False.elim (hw₁w₂_nonadj hadj.symm)
    · exact hzw₂.symm

  have witness_for_bad (z : V) (hz : Bad z) :
      ∃ x : V, G.Adj v x ∧ x ∉ closedBall G 1 z := by
    obtain ⟨x, hxv, hxz⟩ := Set.not_subset.mp hz.2.1
    rcases (ball_one_iff v x).1 hxv with hxv_eq | hvx
    · subst x
      exact False.elim
        (hxz ((ball_one_iff z v).2 (Or.inr hz.1.symm)))
    · exact ⟨x, hvx, hxz⟩

  have no_three_bad (z₁ z₂ z₃ : V)
      (hz₁ : Bad z₁) (hz₂ : Bad z₂) (hz₃ : Bad z₃)
      (h₁₂ : z₁ ≠ z₂) (h₁₃ : z₁ ≠ z₃) (h₂₃ : z₂ ≠ z₃) :
      False := by
    have hvz₁ := hz₁.1
    have hvz₂ := hz₂.1
    have hvz₃ := hz₃.1
    have hw₁z₁ := bad_adj_w₁ z₁ hz₁
    have hw₁z₂ := bad_adj_w₁ z₂ hz₂
    have hw₁z₃ := bad_adj_w₁ z₃ hz₃
    have hw₂z₁ := bad_adj_w₂ z₁ hz₁
    have hw₂z₂ := bad_adj_w₂ z₂ hz₂
    have hw₂z₃ := bad_adj_w₂ z₃ hz₃
    have hvz₁_ne := hvz₁.ne
    have hvz₂_ne := hvz₂.ne
    have hvz₃_ne := hvz₃.ne
    have hw₁z₁_ne := hw₁z₁.ne
    have hw₁z₂_ne := hw₁z₂.ne
    have hw₁z₃_ne := hw₁z₃.ne
    have hw₂z₁_ne := hw₂z₁.ne
    have hw₂z₂_ne := hw₂z₂.ne
    have hw₂z₃_ne := hw₂z₃.ne
    let f : (Fin 3 ⊕ Fin 3) → V
      | Sum.inl i => ![v, w₁, w₂] i
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

  have finish (W₀ : Finset V)
      (hw₁W₀ : w₁ ∈ W₀) (hw₂W₀ : w₂ ∈ W₀)
      (hW₀neighbors : W₀ ⊆ G.neighborFinset v)
      (hW₀card : W₀.card ≤ 4)
      (hW₀bad :
        ∀ z : V, Bad z →
          ∃ x ∈ W₀, x ∉ closedBall G 1 z) :
      ∃ W : Finset V,
        W.card = 4 ∧
        (∀ w ∈ W, G.Adj v w) ∧
        ∀ w : V, G.Adj v w → ¬ Dominates G 1 v w →
          ∃ x ∈ W, x ∉ closedBall G 1 w := by
    obtain ⟨W, hW₀W, hWneighbors, hWcard⟩ :=
      Finset.exists_subsuperset_card_eq
        hW₀neighbors hW₀card hdegree_finset
    refine ⟨W, hWcard, ?_, ?_⟩
    · intro x hx
      exact (G.mem_neighborFinset v x).1 (hWneighbors hx)
    · intro z hvz hznotdom
      by_cases hw₁z : w₁ ∈ closedBall G 1 z
      · by_cases hw₂z : w₂ ∈ closedBall G 1 z
        · obtain ⟨x, hxW₀, hxz⟩ :=
            hW₀bad z ⟨hvz, hznotdom, hw₁z, hw₂z⟩
          exact ⟨x, hW₀W hxW₀, hxz⟩
        · exact ⟨w₂, hW₀W hw₂W₀, hw₂z⟩
      · exact ⟨w₁, hW₀W hw₁W₀, hw₁z⟩

  by_cases hexception₁ : ∃ z : V, Bad z
  · obtain ⟨z₁, hz₁⟩ := hexception₁
    obtain ⟨x₁, hx₁neighbor, hx₁z₁⟩ := witness_for_bad z₁ hz₁
    by_cases hexception₂ : ∃ z : V, Bad z ∧ z ≠ z₁
    · obtain ⟨z₂, hz₂, hz₂z₁⟩ := hexception₂
      obtain ⟨x₂, hx₂neighbor, hx₂z₂⟩ := witness_for_bad z₂ hz₂
      have classify (z : V) (hz : Bad z) : z = z₁ ∨ z = z₂ := by
        by_contra hnot
        have hnot₁ : z ≠ z₁ := fun h => hnot (Or.inl h)
        have hnot₂ : z ≠ z₂ := fun h => hnot (Or.inr h)
        exact no_three_bad z₁ z₂ z hz₁ hz₂ hz
          hz₂z₁.symm hnot₁.symm hnot₂.symm
      apply finish {w₁, w₂, x₁, x₂}
      · simp
      · simp
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx | hx | hx
        · subst x
          exact hw₁mem
        · subst x
          exact hw₂mem
        · subst x
          exact (G.mem_neighborFinset v x₁).2 hx₁neighbor
        · subst x
          exact (G.mem_neighborFinset v x₂).2 hx₂neighbor
      · exact card_quadruple w₁ w₂ x₁ x₂
      · intro z hz
        rcases classify z hz with rfl | rfl
        · exact ⟨x₁, by simp, hx₁z₁⟩
        · exact ⟨x₂, by simp, hx₂z₂⟩
    · have classify (z : V) (hz : Bad z) : z = z₁ := by
        by_contra hne
        exact hexception₂ ⟨z, hz, hne⟩
      apply finish {w₁, w₂, x₁}
      · simp
      · simp
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx | hx
        · subst x
          exact hw₁mem
        · subst x
          exact hw₂mem
        · subst x
          exact (G.mem_neighborFinset v x₁).2 hx₁neighbor
      · exact (card_triple w₁ w₂ x₁).trans (by omega)
      · intro z hz
        have hz₁eq := classify z hz
        subst z
        exact ⟨x₁, by simp, hx₁z₁⟩
  · apply finish {w₁, w₂}
    · simp
    · simp
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · subst x
        exact hw₁mem
      · subst x
        exact hw₂mem
    · exact (card_pair w₁ w₂).trans (by omega)
    · intro z hz
      exact False.elim (hexception₁ ⟨z, hz⟩)

end Lax16Proofs.CenterSet
