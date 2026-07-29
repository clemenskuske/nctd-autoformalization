import Lax16.OutsideThreeSetGadget

namespace Lax16Proofs.OutsideThreeSetGadget

open Lax16.OutsideThreeSetGadget
open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u v

/-- A direct graph embedding is a topological model with one-edge routes. -/
def directTopologicalModel {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V} (f : W ↪ V)
    (hadj : ∀ {a b : W}, H.Adj a b → G.Adj (f a) (f b)) :
    TopologicalModel H G where
  branch := f
  route h := (hadj h).toWalk
  route_isPath h := SimpleGraph.Walk.IsPath.of_adj (hadj h)
  branch_avoids_interiors h z := by
    change f z ∉ walkInterior (hadj h).toWalk
    simp [walkInterior, SimpleGraph.Adj.toWalk]
    aesop
  route_interiors_disjoint hab hcd _ := by
    change Disjoint (walkInterior (hadj hab).toWalk)
      (walkInterior (hadj hcd).toWalk)
    have hempty : walkInterior (hadj hab).toWalk = ∅ := by
      ext x
      simp [walkInterior, SimpleGraph.Adj.toWalk]
      aesop
    rw [hempty]
    exact disjoint_bot_left

/--
---
conclusion: Lax16.OutsideThreeSetGadget.outside_three_set_gadget
---
Two distinct outside vertices seeing all three selected neighbors, together
with the center and those neighbors, form a direct `K₃,₃`.  Uniqueness then
turns failure of an external certificate into the contradiction that the
outside vertex belongs to the enlarged batch.
-/
theorem outside_three_set_gadget {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hplanar : IsPlanar G)
    (center : V) (Y : Finset V)
    (hcard : Y.card = 3)
    (hneighbors : ∀ y ∈ Y, G.Adj center y) :
    Set.Subsingleton {x : V | OutsideSees G center Y x} ∧
    ∀ x : V, OutsideSees G center Y x →
      (∀ y ∈ insert x Y, y ∈ closedBall G 1 x) ∧
      (insert x Y).card ≤ 4 ∧
      ∀ z : V, z ∉ insert x (closedBallFinset G 1 center) →
        ∃ y ∈ insert x Y, y ∉ closedBall G 1 z := by
  classical
  rcases Finset.card_eq_three.mp hcard with
    ⟨y₁, y₂, y₃, hy₁y₂, hy₁y₃, hy₂y₃, rfl⟩
  have hy₁_adj : G.Adj center y₁ := hneighbors y₁ (by simp)
  have hy₂_adj : G.Adj center y₂ := hneighbors y₂ (by simp)
  have hy₃_adj : G.Adj center y₃ := hneighbors y₃ (by simp)
  have hcenter_ball : center ∈ closedBall G 1 center :=
    ⟨SimpleGraph.Walk.nil, by simp⟩
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
  have hunique :
      Set.Subsingleton
        {x : V | OutsideSees G center {y₁, y₂, y₃} x} := by
    intro x hx z hz
    by_contra hxz
    have hx_out : x ∉ closedBall G 1 center := hx.1
    have hz_out : z ∉ closedBall G 1 center := hz.1
    have hx_center : x ≠ center := by
      intro h
      subst x
      exact hx_out hcenter_ball
    have hz_center : z ≠ center := by
      intro h
      subst z
      exact hz_out hcenter_ball
    have hxy₁ : G.Adj x y₁ := hx.2 y₁ (by simp)
    have hxy₂ : G.Adj x y₂ := hx.2 y₂ (by simp)
    have hxy₃ : G.Adj x y₃ := hx.2 y₃ (by simp)
    have hzy₁ : G.Adj z y₁ := hz.2 y₁ (by simp)
    have hzy₂ : G.Adj z y₂ := hz.2 y₂ (by simp)
    have hzy₃ : G.Adj z y₃ := hz.2 y₃ (by simp)
    let leftFun : Fin 3 → V :=
      fun i => if i = 0 then center else if i = 1 then x else z
    let rightFun : Fin 3 → V :=
      fun i => if i = 0 then y₁ else if i = 1 then y₂ else y₃
    let left : Fin 3 ↪ V :=
      ⟨leftFun, by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp [leftFun, hx_center, hx_center.symm, hz_center,
            hz_center.symm, hxz, Ne.symm hxz] at hij ⊢⟩
    let right : Fin 3 ↪ V :=
      ⟨rightFun, by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp [rightFun, hy₁y₂, hy₁y₂.symm, hy₁y₃,
            hy₁y₃.symm, hy₂y₃, hy₂y₃.symm] at hij ⊢⟩
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
          · exact ((hcross i j).ne hij).elim
          · exact ((hcross j i).ne hij.symm).elim
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
    exact (hplanar.2 ⟨directTopologicalModel branch hadj⟩).elim
  refine ⟨hunique, ?_⟩
  intro x hx
  constructor
  · intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨SimpleGraph.Walk.nil, by simp⟩
    · exact ⟨(hx.2 y hy).toWalk, by simp⟩
  constructor
  · calc
      Finset.card (insert x ({y₁, y₂, y₃} : Finset V))
          ≤ Finset.card ({y₁, y₂, y₃} : Finset V) + 1 :=
            Finset.card_insert_le _ _
      _ = 4 := by omega
  · intro z hz_outside
    by_contra hcertificate
    have hcertificate_all :
        ∀ y ∈ insert x ({y₁, y₂, y₃} : Finset V),
          y ∈ closedBall G 1 z := by
      intro y hy
      by_contra hy_not
      exact hcertificate ⟨y, hy, hy_not⟩
    have hz_not_ball : z ∉ closedBall G 1 center := by
      have hz_not_finset :
          z ∉ closedBallFinset G 1 center := by
        intro hz
        exact hz_outside (Finset.mem_insert_of_mem hz)
      simpa [closedBallFinset] using hz_not_finset
    have hz_sees : OutsideSees G center {y₁, y₂, y₃} z := by
      refine ⟨hz_not_ball, ?_⟩
      intro y hy
      have hy_ball : y ∈ closedBall G 1 z :=
        hcertificate_all y (Finset.mem_insert_of_mem hy)
      rcases (mem_ball_one_iff z y).mp hy_ball with hy_eq | hzy
      · have hz_neighbor : z ∈ closedBall G 1 center := by
          subst y
          rcases Finset.mem_insert.mp hy with hy₁ | hyrest
          · subst z
            exact ⟨hy₁_adj.toWalk, by simp⟩
          · rcases Finset.mem_insert.mp hyrest with hy₂ | hy₃
            · subst z
              exact ⟨hy₂_adj.toWalk, by simp⟩
            · have : z = y₃ := by simpa using hy₃
              subst z
              exact ⟨hy₃_adj.toWalk, by simp⟩
        exact (hz_not_ball hz_neighbor).elim
      · exact hzy
    have hxz : x = z := hunique hx hz_sees
    subst z
    exact hz_outside (Finset.mem_insert_self x _)

end Lax16Proofs.OutsideThreeSetGadget
