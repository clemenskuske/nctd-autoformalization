import Lax60.DominatorCount

namespace Lax60Proofs.DominatorCount

open Lax60.DominatorDefinitions
open Lax60.PlanarGraphs
open Lax60.TeachingMaps

universe u v

/-- An injective copy of a graph gives a topological model using one-edge routes. -/
def directTopologicalModel {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V} (f : W ↪ V)
    (hadj : ∀ {a b : W}, H.Adj a b → G.Adj (f a) (f b)) :
    TopologicalModel H G where
  branch := f
  route h := (hadj h).toWalk
  route_isPath h := SimpleGraph.Walk.IsPath.of_adj (hadj h)
  branch_avoids_interiors h z := by
    rw [show walkInterior (hadj h).toWalk = ∅ by
      ext x
      simp [walkInterior, SimpleGraph.Adj.toWalk]
      aesop]
    simp
  route_interiors_disjoint hab hcd _ := by
    rw [show walkInterior (hadj hab).toWalk = ∅ by
      ext x
      simp [walkInterior, SimpleGraph.Adj.toWalk]
      aesop]
    exact disjoint_bot_left

/--
---
conclusion: Lax60.DominatorCount.dominator_count_bounds
---
Two dominators and three further neighbors give a direct `K₃,₃`.  When the
center has exactly four neighbors, three dominators and the remaining
neighbor give a direct `K₅`.
-/
theorem dominator_count_bounds {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hplanar : IsPlanar G) (center : V) :
    (5 ≤ (G.neighborSet center).ncard →
      (dominatorSet G center).ncard ≤ 1) ∧
    ((G.neighborSet center).ncard = 4 →
      (dominatorSet G center).ncard ≤ 2) := by
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
  have dominator_adj {w x : V} (hw : w ∈ dominatorSet G center)
      (hx : G.Adj center x) (hxw : x ≠ w) : G.Adj w x := by
    have hx_ball : x ∈ closedBall G 1 center :=
      ⟨hx.toWalk, by simp⟩
    have hx_dominated : x ∈ closedBall G 1 w := hw.2 hx_ball
    rcases (mem_ball_one_iff w x).mp hx_dominated with h | h
    · exact (hxw h).elim
    · exact h
  unfold IsPlanar at hplanar
  constructor
  · intro hdegree
    by_contra hbound
    have htwo : 1 < (dominatorSet G center).ncard := by omega
    rcases (Set.one_lt_ncard (s := dominatorSet G center)).mp htwo with
      ⟨w₁, hw₁, w₂, hw₂, hw₁w₂⟩
    have hw₁_adj : G.Adj center w₁ := hw₁.1
    have hw₂_adj : G.Adj center w₂ := hw₂.1
    let P : Set V := {w₁, w₂}
    have hP_subset : P ⊆ G.neighborSet center := by
      intro x hx
      rcases hx with (rfl | rfl)
      · exact hw₁_adj
      · exact hw₂_adj
    have hP_card : P.ncard = 2 := Set.ncard_pair hw₁w₂
    have hremaining : 2 < ((G.neighborSet center) \ P).ncard := by
      rw [Set.ncard_diff hP_subset, hP_card]
      omega
    rcases (Set.two_lt_ncard_iff
      (s := (G.neighborSet center) \ P)).mp hremaining with
      ⟨x₁, x₂, x₃, hx₁, hx₂, hx₃, hx₁x₂, hx₁x₃, hx₂x₃⟩
    have hx₁_not : x₁ ≠ w₁ ∧ x₁ ≠ w₂ := by
      simpa [P] using hx₁.2
    have hx₂_not : x₂ ≠ w₁ ∧ x₂ ≠ w₂ := by
      simpa [P] using hx₂.2
    have hx₃_not : x₃ ≠ w₁ ∧ x₃ ≠ w₂ := by
      simpa [P] using hx₃.2
    have hx₁_center : x₁ ≠ center := hx₁.1.ne.symm
    have hx₂_center : x₂ ≠ center := hx₂.1.ne.symm
    have hx₃_center : x₃ ≠ center := hx₃.1.ne.symm
    have hx₁_adj : G.Adj center x₁ := hx₁.1
    have hx₂_adj : G.Adj center x₂ := hx₂.1
    have hx₃_adj : G.Adj center x₃ := hx₃.1
    have hw₁x₁ : G.Adj w₁ x₁ := dominator_adj hw₁ hx₁.1 hx₁_not.1
    have hw₁x₂ : G.Adj w₁ x₂ := dominator_adj hw₁ hx₂.1 hx₂_not.1
    have hw₁x₃ : G.Adj w₁ x₃ := dominator_adj hw₁ hx₃.1 hx₃_not.1
    have hw₂x₁ : G.Adj w₂ x₁ := dominator_adj hw₂ hx₁.1 hx₁_not.2
    have hw₂x₂ : G.Adj w₂ x₂ := dominator_adj hw₂ hx₂.1 hx₂_not.2
    have hw₂x₃ : G.Adj w₂ x₃ := dominator_adj hw₂ hx₃.1 hx₃_not.2
    let leftFun : Fin 3 → V :=
      fun i => if i = 0 then center else if i = 1 then w₁ else w₂
    let rightFun : Fin 3 → V :=
      fun i => if i = 0 then x₁ else if i = 1 then x₂ else x₃
    let left : Fin 3 ↪ V :=
      ⟨leftFun, by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp [leftFun, hw₁_adj.ne, hw₁_adj.ne.symm, hw₂_adj.ne,
            hw₂_adj.ne.symm, hw₁w₂, hw₁w₂.symm] at hij ⊢⟩
    let right : Fin 3 ↪ V :=
      ⟨rightFun, by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp [rightFun, hx₁x₂, hx₁x₂.symm, hx₁x₃, hx₁x₃.symm,
            hx₂x₃, hx₂x₃.symm] at hij ⊢⟩
    have hleft_right : ∀ i j, left i ≠ right j := by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [left, right, leftFun, rightFun, hx₁_center, hx₁_center.symm,
          hx₂_center, hx₂_center.symm, hx₃_center, hx₃_center.symm,
          hx₁_not, hx₁_not.1.symm, hx₁_not.2.symm,
          hx₂_not, hx₂_not.1.symm, hx₂_not.2.symm,
          hx₃_not, hx₃_not.1.symm, hx₃_not.2.symm]
    have hcross : ∀ i j, G.Adj (left i) (right j) := by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [left, right, leftFun, rightFun] <;> assumption
    let branch : Sum (Fin 3) (Fin 3) ↪ V :=
      { toFun
          | Sum.inl i => left i
          | Sum.inr j => right j
        inj' := by
          rintro (i | i) (j | j) hij
          · exact congrArg Sum.inl (left.injective hij)
          · exact (hleft_right i j hij).elim
          · exact (hleft_right j i hij.symm).elim
          · exact congrArg Sum.inr (right.injective hij) }
    have hadj : ∀ {a b : Sum (Fin 3) (Fin 3)},
        (completeBipartiteGraph (Fin 3) (Fin 3)).Adj a b →
        G.Adj (branch a) (branch b) := by
      intro a b hab
      rcases a with i | i <;> rcases b with j | j
      · simp at hab
      · exact hcross i j
      · exact (hcross j i).symm
      · simp at hab
    exact hplanar.2 ⟨directTopologicalModel branch hadj⟩
  · intro hdegree
    by_contra hbound
    have hthree : 2 < (dominatorSet G center).ncard := by omega
    rcases (Set.two_lt_ncard_iff
      (s := dominatorSet G center)).mp hthree with
      ⟨w₁, w₂, w₃, hw₁, hw₂, hw₃, hw₁w₂, hw₁w₃, hw₂w₃⟩
    have hw₁_adj : G.Adj center w₁ := hw₁.1
    have hw₂_adj : G.Adj center w₂ := hw₂.1
    have hw₃_adj : G.Adj center w₃ := hw₃.1
    let P : Set V := {w₁, w₂, w₃}
    have hP_subset : P ⊆ G.neighborSet center := by
      intro x hx
      simp only [P, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hw₁_adj
      · exact hw₂_adj
      · exact hw₃_adj
    have hP_card : P.ncard = 3 := by
      rw [show P = {w₁, w₂, w₃} from rfl,
        Set.ncard_insert_of_notMem (by simpa [hw₁w₂, hw₁w₃]),
        Set.ncard_pair hw₂w₃]
    have hP_lt : P.ncard < (G.neighborSet center).ncard := by
      omega
    rcases Set.exists_mem_notMem_of_ncard_lt_ncard hP_lt with
      ⟨x, hx_neighbor, hx_not_P⟩
    have hx_not : x ≠ w₁ ∧ x ≠ w₂ ∧ x ≠ w₃ := by
      simpa [P] using hx_not_P
    have hx_center : x ≠ center := hx_neighbor.ne.symm
    have hx_adj : G.Adj center x := hx_neighbor
    have hw₁w₂_adj : G.Adj w₁ w₂ :=
      dominator_adj hw₁ hw₂_adj hw₁w₂.symm
    have hw₁w₃_adj : G.Adj w₁ w₃ :=
      dominator_adj hw₁ hw₃_adj hw₁w₃.symm
    have hw₂w₃_adj : G.Adj w₂ w₃ :=
      dominator_adj hw₂ hw₃_adj hw₂w₃.symm
    have hw₁x : G.Adj w₁ x := dominator_adj hw₁ hx_neighbor hx_not.1
    have hw₂x : G.Adj w₂ x := dominator_adj hw₂ hx_neighbor hx_not.2.1
    have hw₃x : G.Adj w₃ x := dominator_adj hw₃ hx_neighbor hx_not.2.2
    let branchFun : Fin 5 → V :=
      fun i => if i = 0 then center else if i = 1 then w₁ else
        if i = 2 then w₂ else if i = 3 then w₃ else x
    let branch : Fin 5 ↪ V :=
      ⟨branchFun, by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp [branchFun, hw₁_adj.ne, hw₁_adj.ne.symm, hw₂_adj.ne,
            hw₂_adj.ne.symm, hw₃_adj.ne, hw₃_adj.ne.symm, hx_center,
            hx_center.symm, hw₁w₂, hw₁w₂.symm, hw₁w₃, hw₁w₃.symm,
            hw₂w₃, hw₂w₃.symm, hx_not, hx_not.1.symm,
            hx_not.2.1.symm, hx_not.2.2.symm] at hij ⊢⟩
    have hadj : ∀ {i j : Fin 5}, (⊤ : SimpleGraph (Fin 5)).Adj i j →
        G.Adj (branch i) (branch j) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [branch, branchFun, hw₁_adj, hw₂_adj, hw₃_adj, hx_adj,
          hw₁w₂_adj, hw₁w₃_adj, hw₂w₃_adj, hw₁x, hw₂x, hw₃x,
          SimpleGraph.adj_comm] at hij ⊢
    exact hplanar.1 ⟨directTopologicalModel branch hadj⟩

end Lax60Proofs.DominatorCount
