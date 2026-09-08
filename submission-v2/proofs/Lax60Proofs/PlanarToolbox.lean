import Lax60.PlanarGraphs

namespace Lax60Proofs.PlanarToolbox

open Lax60.PlanarGraphs

universe u v w

/-- Forget the subtype restriction on a walk in an induced graph. -/
def liftInducedWalk {V : Type u} {G : SimpleGraph V} {s : Set V}
    {a b : s} (p : (G.induce s).Walk a b) :
    G.Walk a.1 b.1 :=
  p.map (SimpleGraph.Embedding.induce s).toHom

lemma walkInterior_liftInducedWalk {V : Type u} {G : SimpleGraph V}
    {s : Set V} {a b : s} (p : (G.induce s).Walk a b) :
    walkInterior (liftInducedWalk p) =
      Subtype.val '' walkInterior p := by
  ext x
  constructor
  · rintro ⟨hx_support, hxa, hxb⟩
    change x ∈ (p.map (SimpleGraph.Embedding.induce s).toHom).support at hx_support
    rw [SimpleGraph.Walk.support_map
      (SimpleGraph.Embedding.induce s).toHom p] at hx_support
    rcases List.mem_map.mp hx_support with ⟨y, hy_support, rfl⟩
    refine ⟨y, ⟨hy_support, ?_, ?_⟩, rfl⟩
    · exact fun h => hxa (congrArg Subtype.val h)
    · exact fun h => hxb (congrArg Subtype.val h)
  · rintro ⟨y, ⟨hy_support, hya, hyb⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · change (y : V) ∈ (p.map (SimpleGraph.Embedding.induce s).toHom).support
      rw [SimpleGraph.Walk.support_map
        (SimpleGraph.Embedding.induce s).toHom p]
      exact List.mem_map.mpr ⟨y, hy_support, rfl⟩
    · exact fun h => hya (Subtype.ext h)
    · exact fun h => hyb (Subtype.ext h)

lemma walkInterior_toWalk_eq_empty {V : Type u} {G : SimpleGraph V}
    {a b : V} (h : G.Adj a b) :
    walkInterior h.toWalk = ∅ := by
  ext x
  simp only [walkInterior, SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
    SimpleGraph.Walk.support_nil, List.mem_cons, List.mem_singleton, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false]
  aesop

/-- Reindex the branch vertices of a topological model along an equivalence. -/
def reindexModel {W : Type u} {W' : Type v} {V : Type w}
    {H : SimpleGraph W} {H' : SimpleGraph W'} {G : SimpleGraph V}
    (e : W' ≃ W)
    (hadj : ∀ a b, H'.Adj a b → H.Adj (e a) (e b))
    (M : TopologicalModel H G) :
    TopologicalModel H' G where
  branch := e.toEmbedding.trans M.branch
  route h := M.route (hadj _ _ h)
  route_isPath h := M.route_isPath (hadj _ _ h)
  branch_avoids_interiors h z :=
    M.branch_avoids_interiors (hadj _ _ h) (e z)
  route_interiors_disjoint hab hcd hne := by
    apply M.route_interiors_disjoint
    intro hold
    apply hne
    rcases hold with hold | hold
    · exact Or.inl ⟨e.injective hold.1, e.injective hold.2⟩
    · exact Or.inr ⟨e.injective hold.1, e.injective hold.2⟩

/-- Add a new branch vertex at the center of a neighbor layer model. -/
def coneBranch {W : Type u} {V : Type v} {H : SimpleGraph W}
    {G : SimpleGraph V} (center : V)
    (M : TopologicalModel H (G.induce (G.neighborSet center))) :
    Option W ↪ V where
  toFun
    | none => center
    | some a => M.branch a
  inj' := by
    rintro (_ | a) (_ | b) h
    · rfl
    · exact ((M.branch b).property.ne h).elim
    · exact ((M.branch a).property.ne h.symm).elim
    · congr 1
      exact M.branch.injective (Subtype.ext h)

/-- Routes in the cone over a complete topological model. -/
def coneCompleteRoute {W : Type u} {V : Type v} {G : SimpleGraph V}
    (center : V)
    (M : TopologicalModel (⊤ : SimpleGraph W)
      (G.induce (G.neighborSet center)))
    {a b : Option W} (h : (⊤ : SimpleGraph (Option W)).Adj a b) :
    G.Walk (coneBranch center M a) (coneBranch center M b) := by
  cases a with
  | none =>
      cases b with
      | none => simpa using h
      | some b => exact (M.branch b).property.toWalk
  | some a =>
      cases b with
      | none => exact (M.branch a).property.symm.toWalk
      | some b =>
          exact liftInducedWalk (M.route (by simpa using h))

lemma coneCompleteRoute_isPath {W : Type u} {V : Type v}
    {G : SimpleGraph V} (center : V)
    (M : TopologicalModel (⊤ : SimpleGraph W)
      (G.induce (G.neighborSet center)))
    {a b : Option W} (h : (⊤ : SimpleGraph (Option W)).Adj a b) :
    (coneCompleteRoute center M h).IsPath := by
  cases a with
  | none =>
      cases b with
      | none => simpa using h
      | some b => exact SimpleGraph.Walk.IsPath.of_adj (M.branch b).property
  | some a =>
      cases b with
      | none => exact SimpleGraph.Walk.IsPath.of_adj (M.branch a).property.symm
      | some b =>
          apply SimpleGraph.Walk.map_isPath_of_injective Subtype.val_injective
          exact M.route_isPath (by simpa using h)

lemma coneCompleteRoute_branch_avoids {W : Type u} {V : Type v}
    {G : SimpleGraph V} (center : V)
    (M : TopologicalModel (⊤ : SimpleGraph W)
      (G.induce (G.neighborSet center)))
    {a b : Option W} (h : (⊤ : SimpleGraph (Option W)).Adj a b)
    (z : Option W) :
    coneBranch center M z ∉ walkInterior (coneCompleteRoute center M h) := by
  cases a with
  | none =>
      cases b with
      | none => simpa using h
      | some b =>
          change coneBranch center M z ∉
            walkInterior (M.branch b).property.toWalk
          rw [walkInterior_toWalk_eq_empty]
          simp
  | some a =>
      cases b with
      | none =>
          change coneBranch center M z ∉
            walkInterior (M.branch a).property.symm.toWalk
          rw [walkInterior_toWalk_eq_empty]
          simp
      | some b =>
          change coneBranch center M z ∉
            walkInterior (liftInducedWalk (M.route (by simpa using h)))
          rw [walkInterior_liftInducedWalk]
          cases z with
          | none =>
              rintro ⟨y, _, hy⟩
              exact y.property.ne hy.symm
          | some z =>
              rintro ⟨y, hy, hyz⟩
              have hy_eq : y = M.branch z := Subtype.ext hyz
              subst y
              exact M.branch_avoids_interiors (by simpa using h) z hy

lemma coneCompleteRoute_interiors_disjoint {W : Type u} {V : Type v}
    {G : SimpleGraph V} (center : V)
    (M : TopologicalModel (⊤ : SimpleGraph W)
      (G.induce (G.neighborSet center)))
    {a b c d : Option W}
    (hab : (⊤ : SimpleGraph (Option W)).Adj a b)
    (hcd : (⊤ : SimpleGraph (Option W)).Adj c d)
    (hne : ¬((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    Disjoint (walkInterior (coneCompleteRoute center M hab))
      (walkInterior (coneCompleteRoute center M hcd)) := by
  cases a with
  | none =>
      cases b with
      | none => simpa using hab
      | some b =>
          change Disjoint (walkInterior (M.branch b).property.toWalk)
            (walkInterior (coneCompleteRoute center M hcd))
          rw [walkInterior_toWalk_eq_empty]
          exact disjoint_bot_left
  | some a =>
      cases b with
      | none =>
          change Disjoint (walkInterior (M.branch a).property.symm.toWalk)
            (walkInterior (coneCompleteRoute center M hcd))
          rw [walkInterior_toWalk_eq_empty]
          exact disjoint_bot_left
      | some b =>
          cases c with
          | none =>
              cases d with
              | none => simpa using hcd
              | some d =>
                  change Disjoint
                    (walkInterior (liftInducedWalk
                      (M.route (by simpa using hab))))
                    (walkInterior (M.branch d).property.toWalk)
                  rw [walkInterior_toWalk_eq_empty]
                  exact disjoint_bot_right
          | some c =>
              cases d with
              | none =>
                  change Disjoint
                    (walkInterior (liftInducedWalk
                      (M.route (by simpa using hab))))
                    (walkInterior (M.branch c).property.symm.toWalk)
                  rw [walkInterior_toWalk_eq_empty]
                  exact disjoint_bot_right
              | some d =>
                  change Disjoint
                    (walkInterior (liftInducedWalk
                      (M.route (by simpa using hab))))
                    (walkInterior (liftInducedWalk
                      (M.route (by simpa using hcd))))
                  rw [walkInterior_liftInducedWalk,
                    walkInterior_liftInducedWalk]
                  apply Set.disjoint_image_of_injective Subtype.val_injective
                  apply M.route_interiors_disjoint
                  intro hold
                  apply hne
                  rcases hold with hold | hold
                  · exact Or.inl
                      ⟨congrArg Option.some hold.1,
                        congrArg Option.some hold.2⟩
                  · exact Or.inr
                      ⟨congrArg Option.some hold.1,
                        congrArg Option.some hold.2⟩

/-- The graph-theoretic cone over a graph. -/
def coneGraph {W : Type u} (H : SimpleGraph W) : SimpleGraph (Option W) where
  Adj a b :=
    match a, b with
    | none, none => False
    | none, some _ => True
    | some _, none => True
    | some x, some y => H.Adj x y
  symm := by
    rintro (_ | a) (_ | b) h <;> simp_all [SimpleGraph.adj_comm]
  loopless := ⟨by
    rintro (_ | a) h
    · exact h
    · exact H.loopless.irrefl a h⟩

/-- Routes in a cone over an arbitrary neighbor-layer model. -/
def coneRoute {W : Type u} {V : Type v} {H : SimpleGraph W}
    {G : SimpleGraph V} (center : V)
    (M : TopologicalModel H (G.induce (G.neighborSet center)))
    {a b : Option W} (h : (coneGraph H).Adj a b) :
    G.Walk (coneBranch center M a) (coneBranch center M b) := by
  cases a with
  | none =>
      cases b with
      | none => exact h.elim
      | some b => exact (M.branch b).property.toWalk
  | some a =>
      cases b with
      | none => exact (M.branch a).property.symm.toWalk
      | some b => exact liftInducedWalk (M.route h)

lemma coneRoute_isPath {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V} (center : V)
    (M : TopologicalModel H (G.induce (G.neighborSet center)))
    {a b : Option W} (h : (coneGraph H).Adj a b) :
    (coneRoute center M h).IsPath := by
  cases a with
  | none =>
      cases b with
      | none => exact h.elim
      | some b => exact SimpleGraph.Walk.IsPath.of_adj (M.branch b).property
  | some a =>
      cases b with
      | none => exact SimpleGraph.Walk.IsPath.of_adj (M.branch a).property.symm
      | some b =>
          apply SimpleGraph.Walk.map_isPath_of_injective Subtype.val_injective
          exact M.route_isPath h

lemma coneRoute_branch_avoids {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V} (center : V)
    (M : TopologicalModel H (G.induce (G.neighborSet center)))
    {a b : Option W} (h : (coneGraph H).Adj a b) (z : Option W) :
    coneBranch center M z ∉ walkInterior (coneRoute center M h) := by
  cases a with
  | none =>
      cases b with
      | none => exact h.elim
      | some b =>
          change coneBranch center M z ∉
            walkInterior (M.branch b).property.toWalk
          rw [walkInterior_toWalk_eq_empty]
          simp
  | some a =>
      cases b with
      | none =>
          change coneBranch center M z ∉
            walkInterior (M.branch a).property.symm.toWalk
          rw [walkInterior_toWalk_eq_empty]
          simp
      | some b =>
          change coneBranch center M z ∉
            walkInterior (liftInducedWalk (M.route h))
          rw [walkInterior_liftInducedWalk]
          cases z with
          | none =>
              rintro ⟨y, _, hy⟩
              exact y.property.ne hy.symm
          | some z =>
              rintro ⟨y, hy, hyz⟩
              have hy_eq : y = M.branch z := Subtype.ext hyz
              subst y
              exact M.branch_avoids_interiors h z hy

lemma coneRoute_interiors_disjoint {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V} (center : V)
    (M : TopologicalModel H (G.induce (G.neighborSet center)))
    {a b c d : Option W}
    (hab : (coneGraph H).Adj a b) (hcd : (coneGraph H).Adj c d)
    (hne : ¬((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    Disjoint (walkInterior (coneRoute center M hab))
      (walkInterior (coneRoute center M hcd)) := by
  cases a with
  | none =>
      cases b with
      | none => exact hab.elim
      | some b =>
          change Disjoint (walkInterior (M.branch b).property.toWalk)
            (walkInterior (coneRoute center M hcd))
          rw [walkInterior_toWalk_eq_empty]
          exact disjoint_bot_left
  | some a =>
      cases b with
      | none =>
          change Disjoint (walkInterior (M.branch a).property.symm.toWalk)
            (walkInterior (coneRoute center M hcd))
          rw [walkInterior_toWalk_eq_empty]
          exact disjoint_bot_left
      | some b =>
          cases c with
          | none =>
              cases d with
              | none => exact hcd.elim
              | some d =>
                  change Disjoint
                    (walkInterior (liftInducedWalk (M.route hab)))
                    (walkInterior (M.branch d).property.toWalk)
                  rw [walkInterior_toWalk_eq_empty]
                  exact disjoint_bot_right
          | some c =>
              cases d with
              | none =>
                  change Disjoint
                    (walkInterior (liftInducedWalk (M.route hab)))
                    (walkInterior (M.branch c).property.symm.toWalk)
                  rw [walkInterior_toWalk_eq_empty]
                  exact disjoint_bot_right
              | some d =>
                  change Disjoint
                    (walkInterior (liftInducedWalk (M.route hab)))
                    (walkInterior (liftInducedWalk (M.route hcd)))
                  rw [walkInterior_liftInducedWalk,
                    walkInterior_liftInducedWalk]
                  apply Set.disjoint_image_of_injective Subtype.val_injective
                  apply M.route_interiors_disjoint
                  intro hold
                  apply hne
                  rcases hold with hold | hold
                  · exact Or.inl
                      ⟨congrArg Option.some hold.1,
                        congrArg Option.some hold.2⟩
                  · exact Or.inr
                      ⟨congrArg Option.some hold.1,
                        congrArg Option.some hold.2⟩

def coneModel {W : Type u} {V : Type v} {H : SimpleGraph W}
    {G : SimpleGraph V} (center : V)
    (M : TopologicalModel H (G.induce (G.neighborSet center))) :
    TopologicalModel (coneGraph H) G where
  branch := coneBranch center M
  route := coneRoute center M
  route_isPath := coneRoute_isPath center M
  branch_avoids_interiors := coneRoute_branch_avoids center M
  route_interiors_disjoint := coneRoute_interiors_disjoint center M

/-- Move an optional left summand outside a sum. -/
def sumOptionEquiv {A : Type u} {B : Type v} :
    Sum (Option A) B ≃ Option (Sum A B) where
  toFun
    | Sum.inl none => none
    | Sum.inl (some a) => some (Sum.inl a)
    | Sum.inr b => some (Sum.inr b)
  invFun
    | none => Sum.inl none
    | some (Sum.inl a) => Sum.inl (some a)
    | some (Sum.inr b) => Sum.inr b
  left_inv := by rintro ((_ | a) | b) <;> rfl
  right_inv := by rintro (_ | (a | b)) <;> rfl

/--
Cone a forbidden subdivision in the neighbor layer from the center.  A
topological `K₄` becomes a topological `K₅`; a topological `K₂,₃` becomes a
topological `K₃,₃`.  Lifted old routes retain their disjoint interiors, and
all newly added routes are single edges with empty interior.
-/
lemma neighbor_layer_outerplanar {V : Type u} {G : SimpleGraph V}
    (hplanar : IsPlanar G) (center : V) :
    IsOuterplanar (G.induce (G.neighborSet center)) := by
  unfold IsPlanar at hplanar
  unfold IsOuterplanar HasTopologicalModel
  constructor
  · rintro ⟨M⟩
    apply hplanar.1
    let e : Fin 5 ≃ Option (Fin 4) := finSuccEquiv 4
    have hadj : ∀ a b : Fin 5, (⊤ : SimpleGraph (Fin 5)).Adj a b →
        (coneGraph (⊤ : SimpleGraph (Fin 4))).Adj (e a) (e b) := by
      intro a b hab
      have hab_ne : a ≠ b := by simpa using hab
      have he_ne : e a ≠ e b := e.injective.ne hab_ne
      generalize ha : e a = oa at he_ne
      generalize hb : e b = ob at he_ne
      cases oa <;> cases ob <;> simp_all [coneGraph]
    exact ⟨reindexModel e hadj (coneModel center M)⟩
  · rintro ⟨M⟩
    apply hplanar.2
    let e₁ : Sum (Fin 3) (Fin 3) ≃ Sum (Option (Fin 2)) (Fin 3) :=
      Equiv.sumCongr (finSuccEquiv 2) (Equiv.refl (Fin 3))
    let e : Sum (Fin 3) (Fin 3) ≃ Option (Sum (Fin 2) (Fin 3)) :=
      e₁.trans sumOptionEquiv
    have hadj : ∀ a b : Sum (Fin 3) (Fin 3),
        (completeBipartiteGraph (Fin 3) (Fin 3)).Adj a b →
        (coneGraph (completeBipartiteGraph (Fin 2) (Fin 3))).Adj
          (e a) (e b) := by
      intro a b hab
      rcases a with a | a
      · rcases b with b | b
        · simp at hab
        · generalize ha : finSuccEquiv 2 a = oa
          cases oa <;> simp [e, e₁, sumOptionEquiv, ha, coneGraph]
      · rcases b with b | b
        · generalize hb : finSuccEquiv 2 b = ob
          cases ob <;> simp [e, e₁, sumOptionEquiv, hb, coneGraph]
        · simp at hab
    exact ⟨reindexModel e hadj (coneModel center M)⟩

end Lax60Proofs.PlanarToolbox
