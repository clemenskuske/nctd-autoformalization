import Lax60.SmallDegreeBatch

namespace Lax60Proofs.SmallDegreeBatch

open Lax60.BatchFramework
open Lax60.TeachingMaps

universe u

/--
---
conclusion: Lax60.SmallDegreeBatch.exists_small_degree_batch
assumptions:
  - Lax60.AnchorLabels.anchor_certifies
---
Use the center as an anchor label for every vertex in its closed
neighborhood.  For each ordered pair of batch vertices whose balls have a
forward difference, choose one such witness.  A vertex has at most three
other batch vertices, so its anchor plus these witnesses has width at most
four.
-/
theorem exists_small_degree_batch {V : Type u} [Fintype V]
    (G : SimpleGraph V) (v : V)
    (hdegree : (G.neighborSet v).ncard ≤ 3) :
    ∃ B : BatchAssignment G,
      B.vertices = closedBallFinset G 1 v ∧
      IsAdmissible G 4 B := by
  classical
  have mem_ball_one_iff (a b : V) :
      b ∈ closedBall G 1 a ↔ b = a ∨ G.Adj a b := by
    constructor
    · rintro ⟨p, hp⟩
      have hp_cases : p.length = 0 ∨ p.length = 1 := by omega
      rcases hp_cases with hp_zero | hp_one
      · exact Or.inl (SimpleGraph.Walk.eq_of_length_eq_zero hp_zero).symm
      · exact Or.inr (SimpleGraph.Walk.adj_of_length_eq_one hp_one)
    · rintro (rfl | hab)
      · exact ⟨SimpleGraph.Walk.nil, by simp⟩
      · exact ⟨hab.toWalk, by simp⟩
  have mem_ball_one_comm (a b : V) :
      b ∈ closedBall G 1 a ↔ a ∈ closedBall G 1 b := by
    rw [mem_ball_one_iff, mem_ball_one_iff]
    constructor
    · rintro (rfl | hab)
      · exact Or.inl rfl
      · exact Or.inr hab.symm
    · rintro (rfl | hba)
      · exact Or.inl rfl
      · exact Or.inr hba.symm
  let C : Finset V := closedBallFinset G 1 v
  have hC_eq : C = insert v (G.neighborFinset v) := by
    ext w
    simp [C, closedBallFinset, mem_ball_one_iff]
  have hneighbor_card : (G.neighborFinset v).card ≤ 3 := by
    rw [SimpleGraph.neighborFinset_def, ← Set.ncard_eq_toFinset_card']
    exact hdegree
  have hC_card : C.card ≤ 4 := by
    rw [hC_eq]
    exact (Finset.card_insert_le v (G.neighborFinset v)).trans (by omega)
  let HasForwardWitness (a b : V) : Prop :=
    ∃ x : V, IsWitness G 1 x a b
  let pick (a b : V) : V :=
    if h : HasForwardWitness a b then Classical.choose h else a
  have pick_spec {a b : V} (h : HasForwardWitness a b) :
      IsWitness G 1 (pick a b) a b := by
    dsimp [pick]
    rw [dif_pos h]
    exact Classical.choose_spec h
  let eligible (a : V) : Finset V :=
    (C.erase a).filter (HasForwardWitness a)
  let teaching (a : V) : Finset V :=
    insert v ((eligible a).image (pick a))
  have distinct_has_direction {a b : V}
      (hab : DistinctConcepts G 1 a b) :
      HasForwardWitness a b ∨ HasForwardWitness b a := by
    unfold DistinctConcepts at hab
    by_cases hsub : closedBall G 1 a ⊆ closedBall G 1 b
    · right
      have hnsub : ¬closedBall G 1 b ⊆ closedBall G 1 a := by
        intro hreverse
        exact hab (Set.Subset.antisymm hsub hreverse)
      rw [Set.not_subset] at hnsub
      rcases hnsub with ⟨x, hxb, hxa⟩
      exact ⟨x, hxb, hxa⟩
    · left
      rw [Set.not_subset] at hsub
      rcases hsub with ⟨x, hxa, hxb⟩
      exact ⟨x, hxa, hxb⟩
  have picked_mem_teaching {a b : V}
      (hbC : b ∈ C) (hab : DistinctConcepts G 1 a b)
      (hforward : HasForwardWitness a b) :
      pick a b ∈ teaching a := by
    have hne : b ≠ a := by
      intro h
      subst b
      exact hab rfl
    have hb_eligible : b ∈ eligible a := by
      simp only [eligible, Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨hne, hbC⟩, hforward⟩
    simp only [teaching, Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨b, hb_eligible, rfl⟩
  refine ⟨{ vertices := C, teaching := teaching }, rfl, ?_⟩
  unfold IsAdmissible
  constructor
  · intro a x haC hxT
    simp only [teaching, Finset.mem_insert, Finset.mem_image] at hxT
    rcases hxT with hx_eq | ⟨b, hb_eligible, hx_eq⟩
    · subst x
      have ha_ball_v : a ∈ closedBall G 1 v := by
        simpa [C, closedBallFinset] using haC
      exact (mem_ball_one_comm v a).mp ha_ball_v
    · subst x
      have hforward : HasForwardWitness a b :=
        (Finset.mem_filter.mp (by simpa only [eligible] using hb_eligible)).2
      exact (pick_spec hforward).1
  constructor
  · intro a haC
    calc
      (teaching a).card
          ≤ ((eligible a).image (pick a)).card + 1 := by
            exact Finset.card_insert_le _ _
      _ ≤ (eligible a).card + 1 := by
            exact Nat.add_le_add_right Finset.card_image_le 1
      _ ≤ (C.erase a).card + 1 := by
            exact Nat.add_le_add_right
              (Finset.card_le_card (Finset.filter_subset _ _)) 1
      _ = C.card := Finset.card_erase_add_one haC
      _ ≤ 4 := hC_card
  constructor
  · intro a b haC hbC hab
    rcases distinct_has_direction hab with hforward | hbackward
    · refine ⟨pick a b, Or.inl (picked_mem_teaching hbC hab hforward),
          Or.inl (pick_spec hforward)⟩
    · have hba : DistinctConcepts G 1 b a := Ne.symm hab
      refine ⟨pick b a, Or.inr (picked_mem_teaching haC hba hbackward),
          Or.inr (pick_spec hbackward)⟩
  · intro a x haC hx_not_C _
    have hv_teaching : v ∈ teaching a := by
      simp only [teaching, Finset.mem_insert, true_or]
    have hv_not_ball_x : v ∉ closedBall G 1 x := by
      have hx_not_ball_v : x ∉ closedBall G 1 v := by
        simpa [C, closedBallFinset] using hx_not_C
      exact fun hv_ball_x =>
        hx_not_ball_v ((mem_ball_one_comm v x).mpr hv_ball_x)
    exact Lax60.AnchorLabels.anchor_certifies hv_teaching x hv_not_ball_x

end Lax60Proofs.SmallDegreeBatch
