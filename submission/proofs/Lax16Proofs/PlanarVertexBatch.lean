import Lax16.PlanarVertexBatch
import Lax16.OuterplanarLayer
import Lax16Proofs.CenterSet
import Lax16Proofs.DominatorCompletion
import Lax16Proofs.OutsideThreeSetGadget
import Lax16Proofs.PlanarToolbox

namespace Lax16Proofs.PlanarVertexBatch

open Lax16.BatchFramework
open Lax16.DominatorDefinitions
open Lax16.OuterplanarLayer
open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u

/--
---
conclusion: Lax16.PlanarVertexBatch.exists_planar_vertex_batch_of_degree_ge_four
assumptions:
  - Lax16.OuterplanarLayer.exists_outerplanar_layer_assignment
---
Use the four-label center set, the completed active-dominator assignments,
and the anchored outerplanar-layer assignments on the remaining neighbors.
The unique possible outside vertex seeing the center set is added to the
batch and receives the outside-gadget assignment.
-/
theorem exists_planar_vertex_batch_of_degree_ge_four {V : Type u}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hplanar : IsPlanar G)
    (v : V) (hdegree : 4 ≤ (G.neighborSet v).ncard) :
    ∃ B : BatchAssignment G,
      closedBallFinset G 1 v ⊆ B.vertices ∧
      (B.vertices \ closedBallFinset G 1 v).card ≤ 1 ∧
      IsAdmissible G 4 B := by
  classical

  have mem_ball_one_iff (a b : V) :
      b ∈ closedBall G 1 a ↔ b = a ∨ G.Adj a b := by
    constructor
    · rintro ⟨p, hp⟩
      have hp_cases : p.length = 0 ∨ p.length = 1 := by omega
      rcases hp_cases with hp_zero | hp_one
      · exact Or.inl (p.eq_of_length_eq_zero hp_zero).symm
      · exact Or.inr (p.adj_of_length_eq_one hp_one)
    · rintro (rfl | hab)
      · exact ⟨SimpleGraph.Walk.nil, by simp⟩
      · exact ⟨hab.toWalk, by simp⟩

  have ball_symm (a b : V) :
      b ∈ closedBall G 1 a ↔ a ∈ closedBall G 1 b := by
    rw [mem_ball_one_iff, mem_ball_one_iff]
    constructor
    · rintro (rfl | hab)
      · exact Or.inl rfl
      · exact Or.inr hab.symm
    · rintro (rfl | hba)
      · exact Or.inl rfl
      · exact Or.inr hba.symm

  let X : Finset V := G.neighborFinset v
  let C : Finset V := closedBallFinset G 1 v

  have mem_X_iff (w : V) : w ∈ X ↔ G.Adj v w := by
    simp [X]

  have mem_C_iff (w : V) :
      w ∈ C ↔ w = v ∨ w ∈ X := by
    rw [show w ∈ C ↔ w ∈ closedBall G 1 v by
      simp [C, closedBallFinset]]
    rw [mem_ball_one_iff, mem_X_iff]

  obtain ⟨W, hWcard, hWneighbors, hWseparates⟩ :=
    Lax16Proofs.CenterSet.exists_center_set G hplanar v hdegree

  obtain ⟨Y, hYW, hYcard⟩ :
      ∃ Y : Finset V, Y ⊆ W ∧ Y.card = 3 := by
    obtain ⟨Y, hYW, hYcard⟩ :=
      Finset.exists_subset_card_eq (s := W) (n := 3) (by omega)
    exact ⟨Y, hYW, hYcard⟩

  have hYneighbors : ∀ y ∈ Y, G.Adj v y := by
    intro y hy
    exact hWneighbors y (hYW hy)

  obtain ⟨hYunique, hYgadget⟩ :=
    Lax16Proofs.OutsideThreeSetGadget.outside_three_set_gadget
      G hplanar v Y hYcard hYneighbors

  let O : Finset V :=
    Finset.univ.filter fun x => OutsideSees G v W x

  have mem_O_iff (x : V) :
      x ∈ O ↔ OutsideSees G v W x := by
    simp [O]

  have outside_Y_of_mem_O {x : V} (hx : x ∈ O) :
      OutsideSees G v Y x := by
    have hxW : OutsideSees G v W x := (mem_O_iff x).mp hx
    exact ⟨hxW.1, fun y hy => hxW.2 y (hYW hy)⟩

  have hOcard : O.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro x z hx hz
    exact hYunique
      (outside_Y_of_mem_O (x := x) hx)
      (outside_Y_of_mem_O (x := z) hz)

  obtain ⟨D, hD⟩ :=
    Lax16Proofs.DominatorCompletion.exists_dominator_completion
      G hplanar v hdegree

  have hXneighbors : ∀ w ∈ X, G.Adj v w := by
    intro w hw
    exact (mem_X_iff w).mp hw

  have houterX :
      IsOuterplanar (G.induce (↑X : Set V)) := by
    have hXset : (↑X : Set V) = G.neighborSet v := by
      ext w
      simp [X]
    rw [hXset]
    exact Lax16Proofs.PlanarToolbox.neighbor_layer_outerplanar hplanar v

  obtain ⟨S, hSlayer, hSanchored, hSexternal⟩ :=
    Lax16.OuterplanarLayer.exists_outerplanar_layer_assignment
      G v X hXneighbors houterX

  let T : TeachingMap V 1 := fun z =>
    if z = v then W
    else if IsActiveDominator G v z then D z
    else if z ∈ X then anchoredTeaching v S z
    else if z ∈ O then insert z Y
    else ∅

  have T_center : T v = W := by
    simp [T]

  have active_ne_center {w : V} (hw : IsActiveDominator G v w) :
      w ≠ v :=
    hw.1.1.ne.symm

  have T_active {w : V} (hw : IsActiveDominator G v w) :
      T w = D w := by
    simp [T, active_ne_center hw, hw]

  have T_neighbor {w : V} (hwX : w ∈ X)
      (hw : ¬ IsActiveDominator G v w) :
      T w = anchoredTeaching v S w := by
    have hwv : w ≠ v := ((mem_X_iff w).mp hwX).ne.symm
    simp [T, hwv, hw, hwX]

  have outside_ne_center {x : V} (hx : x ∈ O) :
      x ≠ v := by
    intro hxv
    subst x
    exact (outside_Y_of_mem_O hx).1
      ⟨SimpleGraph.Walk.nil, by simp⟩

  have outside_not_neighbor {x : V} (hx : x ∈ O) :
      x ∉ X := by
    intro hxX
    have hxball : x ∈ closedBall G 1 v :=
      (mem_ball_one_iff v x).2 (Or.inr ((mem_X_iff x).mp hxX))
    exact (outside_Y_of_mem_O hx).1 hxball

  have outside_not_active {x : V} (hx : x ∈ O) :
      ¬ IsActiveDominator G v x := by
    intro hactive
    exact outside_not_neighbor hx
      ((mem_X_iff x).2 hactive.1.1)

  have T_outside {x : V} (hx : x ∈ O) :
      T x = insert x Y := by
    simp [T, outside_ne_center hx, outside_not_active hx,
      outside_not_neighbor hx, hx]

  let B : BatchAssignment G :=
    { vertices := C ∪ O
      teaching := T }

  refine ⟨B, ?_, ?_, ?_⟩
  · intro x hx
    exact Finset.mem_union_left O hx
  · calc
      (B.vertices \ C).card ≤ O.card := by
        apply Finset.card_le_card
        intro x hx
        change x ∈ (C ∪ O) \ C at hx
        have hx' := Finset.mem_sdiff.mp hx
        exact (Finset.mem_union.mp hx'.1).resolve_left hx'.2
      _ ≤ 1 := hOcard
  · unfold IsAdmissible
    constructor
    · intro a x haB hxT
      change a ∈ C ∪ O at haB
      change x ∈ T a at hxT
      rcases Finset.mem_union.mp haB with haC | haO
      · rcases (mem_C_iff a).mp haC with ha_eq | haX
        · subst a
          rw [T_center] at hxT
          exact (mem_ball_one_iff v x).2
            (Or.inr (hWneighbors x hxT))
        · by_cases ha_active : IsActiveDominator G v a
          · rw [T_active ha_active] at hxT
            exact (hD.1 a ha_active).2.2.1 x hxT
          · rw [T_neighbor haX ha_active] at hxT
            exact (hSanchored a haX).2 x hxT
      · rw [T_outside haO] at hxT
        exact (hYgadget a (outside_Y_of_mem_O haO)).1 x hxT
    · constructor
      · intro a haB
        change a ∈ C ∪ O at haB
        change (T a).card ≤ 4
        rcases Finset.mem_union.mp haB with haC | haO
        · rcases (mem_C_iff a).mp haC with ha_eq | haX
          · subst a
            simpa [T_center] using hWcard.le
          · by_cases ha_active : IsActiveDominator G v a
            · rw [T_active ha_active]
              exact (hD.1 a ha_active).1
            · rw [T_neighbor haX ha_active]
              exact (hSanchored a haX).1
        · rw [T_outside haO]
          exact (hYgadget a (outside_Y_of_mem_O haO)).2.1
      · constructor
        · intro a b haB hbB hab
          change a ∈ C ∪ O at haB
          change b ∈ C ∪ O at hbB
          change Separates G 1 T a b
          rcases Finset.mem_union.mp haB with haC | haO
          · rcases Finset.mem_union.mp hbB with hbC | hbO
            · rcases (mem_C_iff a).mp haC with ha_eq | haX
              · subst a
                rcases (mem_C_iff b).mp hbC with hb_eq | hbX
                · subst b
                  exact (hab rfl).elim
                · by_cases hb_active : IsActiveDominator G v b
                  · have hteach := hD.1 b hb_active
                    obtain ⟨x, hxD, hxnot⟩ :=
                      hteach.2.2.2 v
                        ((mem_ball_one_iff v v).2 (Or.inl rfl))
                        (fun h => hab h.symm)
                        (by
                          intro hvactive
                          exact hvactive.1.1.ne rfl)
                    refine ⟨x, ?_, Or.inr ?_⟩
                    · exact Or.inr (by
                        rw [T_active hb_active]
                        exact hxD)
                    · exact ⟨hteach.2.2.1 x hxD, hxnot⟩
                  · have hbdom : ¬ Dominates G 1 v b := by
                      intro hbdom
                      exact hb_active
                        ⟨⟨(mem_X_iff b).mp hbX, hbdom⟩,
                          hab⟩
                    obtain ⟨x, hxW, hxnot⟩ :=
                      hWseparates b ((mem_X_iff b).mp hbX) hbdom
                    refine ⟨x, Or.inl ?_, Or.inl ?_⟩
                    · simpa [T_center] using hxW
                    · exact ⟨(mem_ball_one_iff v x).2
                        (Or.inr (hWneighbors x hxW)), hxnot⟩
              · rcases (mem_C_iff b).mp hbC with hb_eq | hbX
                · subst b
                  by_cases ha_active : IsActiveDominator G v a
                  · have hteach := hD.1 a ha_active
                    obtain ⟨x, hxD, hxnot⟩ :=
                      hteach.2.2.2 v
                        ((mem_ball_one_iff v v).2 (Or.inl rfl))
                        hab
                        (by
                          intro hvactive
                          exact hvactive.1.1.ne rfl)
                    refine ⟨x, Or.inl ?_, Or.inl ?_⟩
                    · rw [T_active ha_active]
                      exact hxD
                    · exact ⟨hteach.2.2.1 x hxD, hxnot⟩
                  · have hadom : ¬ Dominates G 1 v a := by
                      intro hadom
                      exact ha_active
                        ⟨⟨(mem_X_iff a).mp haX, hadom⟩,
                          fun h => hab h.symm⟩
                    obtain ⟨x, hxW, hxnot⟩ :=
                      hWseparates a ((mem_X_iff a).mp haX) hadom
                    refine ⟨x, Or.inr ?_, Or.inr ?_⟩
                    · simpa [T_center] using hxW
                    · exact ⟨(mem_ball_one_iff v x).2
                        (Or.inr (hWneighbors x hxW)), hxnot⟩
                · by_cases ha_active : IsActiveDominator G v a
                  · by_cases hb_active : IsActiveDominator G v b
                    · have hsep := hD.2 a b ha_active hb_active hab
                      rcases hsep with ⟨x, hxD, hxwitness⟩
                      refine ⟨x, ?_, hxwitness⟩
                      rcases hxD with hxDa | hxDb
                      · exact Or.inl (by
                          rw [T_active ha_active]
                          exact hxDa)
                      · exact Or.inr (by
                          rw [T_active hb_active]
                          exact hxDb)
                    · have hteach := hD.1 a ha_active
                      obtain ⟨x, hxD, hxnot⟩ :=
                        hteach.2.2.2 b
                          ((mem_ball_one_iff v b).2
                            (Or.inr ((mem_X_iff b).mp hbX)))
                          hab hb_active
                      refine ⟨x, Or.inl ?_, Or.inl ?_⟩
                      · rw [T_active ha_active]
                        exact hxD
                      · exact ⟨hteach.2.2.1 x hxD, hxnot⟩
                  · by_cases hb_active : IsActiveDominator G v b
                    · have hteach := hD.1 b hb_active
                      obtain ⟨x, hxD, hxnot⟩ :=
                        hteach.2.2.2 a
                          ((mem_ball_one_iff v a).2
                            (Or.inr ((mem_X_iff a).mp haX)))
                          (fun h => hab h.symm) ha_active
                      refine ⟨x, Or.inr ?_, Or.inr ?_⟩
                      · rw [T_active hb_active]
                        exact hxD
                      · exact ⟨hteach.2.2.1 x hxD, hxnot⟩
                    · have hsep :=
                        hSlayer.2 a b haX hbX hab
                      rcases hsep with ⟨x, hxS, hxwitness⟩
                      refine ⟨x, ?_, hxwitness⟩
                      rcases hxS with hxSa | hxSb
                      · exact Or.inl (by
                          rw [T_neighbor haX ha_active]
                          simpa only [anchoredTeaching, Finset.mem_insert] using
                            (Or.inr hxSa : x = v ∨ x ∈ S a))
                      · exact Or.inr (by
                          rw [T_neighbor hbX hb_active]
                          simpa only [anchoredTeaching, Finset.mem_insert] using
                            (Or.inr hxSb : x = v ∨ x ∈ S b))
            · have haOut := outside_Y_of_mem_O hbO
              rcases (mem_C_iff a).mp haC with ha_eq | haX
              · subst a
                refine ⟨b, Or.inr ?_, Or.inr ?_⟩
                · rw [T_outside hbO]
                  exact Finset.mem_insert_self _ _
                · exact ⟨
                    (mem_ball_one_iff b b).2 (Or.inl rfl),
                    haOut.1⟩
              · have hv_not_ball_b :
                    v ∉ closedBall G 1 b := by
                  exact fun hvb => haOut.1 ((ball_symm v b).2 hvb)
                refine ⟨v, Or.inl ?_, Or.inl ?_⟩
                · by_cases ha_active : IsActiveDominator G v a
                  · rw [T_active ha_active]
                    exact (hD.1 a ha_active).2.1
                  · rw [T_neighbor haX ha_active]
                    simp [anchoredTeaching]
                · exact ⟨(mem_ball_one_iff a v).2
                    (Or.inr ((mem_X_iff a).mp haX).symm),
                    hv_not_ball_b⟩
          · rcases Finset.mem_union.mp hbB with hbC | hbO
            · have haOut := outside_Y_of_mem_O haO
              rcases (mem_C_iff b).mp hbC with hb_eq | hbX
              · subst b
                refine ⟨a, Or.inl ?_, Or.inl ?_⟩
                · rw [T_outside haO]
                  exact Finset.mem_insert_self _ _
                · exact ⟨
                    (mem_ball_one_iff a a).2 (Or.inl rfl),
                    haOut.1⟩
              · have hv_not_ball_a :
                    v ∉ closedBall G 1 a := by
                  exact fun hva => haOut.1 ((ball_symm v a).2 hva)
                refine ⟨v, Or.inr ?_, Or.inr ?_⟩
                · by_cases hb_active : IsActiveDominator G v b
                  · rw [T_active hb_active]
                    exact (hD.1 b hb_active).2.1
                  · rw [T_neighbor hbX hb_active]
                    simp [anchoredTeaching]
                · exact ⟨(mem_ball_one_iff b v).2
                    (Or.inr ((mem_X_iff b).mp hbX).symm),
                    hv_not_ball_a⟩
            · have hab_eq :
                  a = b :=
                hYunique (outside_Y_of_mem_O haO)
                  (outside_Y_of_mem_O hbO)
              subst b
              exact (hab rfl).elim
        · intro a z haB hzB _
          change a ∈ C ∪ O at haB
          change ∃ y ∈ T a, y ∉ closedBall G 1 z
          have hz_not_C : z ∉ C := by
            intro hzC
            exact hzB (Finset.mem_union_left O hzC)
          have hz_not_ball :
              z ∉ closedBall G 1 v := by
            simpa [C, closedBallFinset] using hz_not_C
          rcases Finset.mem_union.mp haB with haC | haO
          · rcases (mem_C_iff a).mp haC with ha_eq | haX
            · subst a
              by_contra hcert
              have hWinside :
                  ∀ y ∈ W, y ∈ closedBall G 1 z := by
                intro y hy
                by_contra hynot
                exact hcert ⟨y, by simpa [T_center] using hy, hynot⟩
              have hzOutsideW : OutsideSees G v W z := by
                refine ⟨hz_not_ball, ?_⟩
                intro y hy
                rcases (mem_ball_one_iff z y).1 (hWinside y hy) with hyz | hzy
                · subst y
                  exact False.elim
                    (hz_not_ball
                      ((mem_ball_one_iff v z).2
                        (Or.inr (hWneighbors z hy))))
                · exact hzy
              exact hzB
                (Finset.mem_union_right C
                  ((mem_O_iff z).2 hzOutsideW))
            · refine ⟨v, ?_, ?_⟩
              · by_cases ha_active : IsActiveDominator G v a
                · rw [T_active ha_active]
                  exact (hD.1 a ha_active).2.1
                · rw [T_neighbor haX ha_active]
                  simp [anchoredTeaching]
              · exact fun hvz => hz_not_ball ((ball_symm v z).2 hvz)
          · have hz_not_insert :
                z ∉ insert a C := by
              simp only [Finset.mem_insert, not_or]
              exact ⟨fun hza => hzB (hza ▸ Finset.mem_union_right C haO),
                hz_not_C⟩
            obtain ⟨y, hy, hynot⟩ :=
              (hYgadget a (outside_Y_of_mem_O haO)).2.2 z hz_not_insert
            refine ⟨y, ?_, hynot⟩
            rw [T_outside haO]
            exact hy

end Lax16Proofs.PlanarVertexBatch
