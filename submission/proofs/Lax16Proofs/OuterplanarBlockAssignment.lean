import Lax16.OuterplanarBlockAssignment
import Lax16Proofs.OuterplanarThetaFinal
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks
import Mathlib.Tactic.FinCases

/-!
This file isolates the graph-theoretic content needed by the exact-two block
assignment.  The structural degree-two theorem is proved by the internal
maximal-theta modules; the remainder is a suppression induction that preserves
an exact two-label positive no-clash assignment.
-/

namespace Lax16Proofs.OuterplanarBlockAssignment

open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u v

set_option maxHeartbeats 1000000

private theorem walkInterior_toWalk_eq_empty
    {V : Type u} {G : SimpleGraph V} {a b : V} (h : G.Adj a b) :
    walkInterior h.toWalk = ∅ := by
  ext z
  simp only [walkInterior, SimpleGraph.Adj.toWalk,
    SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
    List.mem_cons, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  aesop

private def directTopologicalModel
    {W : Type u} {V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
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

private theorem false_of_k23_configuration
    {V : Type u} {G : SimpleGraph V} (houter : IsOuterplanar G)
    (a b x c d : V)
    (hab : a ≠ b)
    (hxc : x ≠ c) (hxd : x ≠ d) (hcd : c ≠ d)
    (hax : G.Adj a x) (hac : G.Adj a c) (had : G.Adj a d)
    (hbx : G.Adj b x) (hbc : G.Adj b c) (hbd : G.Adj b d) :
    False := by
  apply houter.2
  let f : Sum (Fin 2) (Fin 3) → V
    | Sum.inl i => if i = 0 then a else b
    | Sum.inr j => if j = 0 then x else if j = 1 then c else d
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, G.ne_of_adj hax, G.ne_of_adj hac, G.ne_of_adj had,
        G.ne_of_adj hbx, G.ne_of_adj hbc, G.ne_of_adj hbd]
  let hom :
      completeBipartiteGraph (Fin 2) (Fin 3) →g G :=
    { toFun := f
      map_rel' := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [f, completeBipartiteGraph, hax, hac, had, hbx, hbc, hbd,
            SimpleGraph.adj_comm] }
  exact ⟨directTopologicalModel hom hf⟩

private theorem walk_end_mem_of_closed {V : Type u} {G : SimpleGraph V}
    (S : Finset V) {a b : V} (p : G.Walk a b)
    (ha : a ∈ S)
    (hclosed : ∀ ⦃u v : V⦄, u ∈ S → G.Adj u v → v ∈ S) :
    b ∈ S := by
  induction p with
  | nil => exact ha
  | cons huv p ih =>
      exact ih (hclosed ha huv)

/-- Delete `x` and add an edge between two surviving vertices. -/
private noncomputable def suppressAt {V : Type u} [Fintype V]
    (G : SimpleGraph V) (x : V) (a b : {z : V // z ≠ x}) :
    SimpleGraph {z : V // z ≠ x} :=
  G.induce {z : V | z ≠ x} ⊔ SimpleGraph.edge a b

private theorem degree_two_neighbors {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x : V} (hx : G.degree x = 2) :
    ∃ a b : V,
      a ≠ b ∧
      G.Adj x a ∧
      G.Adj x b ∧
      ∀ ⦃z : V⦄, G.Adj x z → z = a ∨ z = b := by
  classical
  have hcard : (G.neighborFinset x).card = 2 := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hx
  obtain ⟨a, b, hab, hneighbors⟩ := Finset.card_eq_two.mp hcard
  refine ⟨a, b, hab, ?_, ?_, ?_⟩
  · have : a ∈ G.neighborFinset x := by
      rw [hneighbors]
      simp
    simpa using this
  · have : b ∈ G.neighborFinset x := by
      rw [hneighbors]
      simp
    simpa using this
  · intro z hxz
    have hz : z ∈ G.neighborFinset x := by simpa using hxz
    rw [hneighbors] at hz
    simpa [eq_comm] using hz

private theorem suppressAt_adj_iff {V : Type u} [Fintype V]
    (G : SimpleGraph V) (x : V)
    (a b p q : {z : V // z ≠ x}) (hab : a ≠ b) :
    (suppressAt G x a b).Adj p q ↔
      G.Adj p.1 q.1 ∨
      (p = a ∧ q = b) ∨
      (p = b ∧ q = a) := by
  classical
  simp only [suppressAt, SimpleGraph.sup_adj, SimpleGraph.induce_adj,
    SimpleGraph.edge_adj]
  change
    (G.Adj p.1 q.1 ∨
      ((p = a ∧ q = b) ∨ (p = b ∧ q = a)) ∧ p ≠ q) ↔
      G.Adj p.1 q.1 ∨
      (p = a ∧ q = b) ∨
      (p = b ∧ q = a)
  constructor
  · rintro (hpq | ⟨hpq, -⟩)
    · exact Or.inl hpq
    · exact Or.inr hpq
  · rintro (hpq | hpq | hpq)
    · exact Or.inl hpq
    · refine Or.inr ⟨Or.inl hpq, ?_⟩
      rintro rfl
      exact hab (hpq.1.symm.trans hpq.2)
    · refine Or.inr ⟨Or.inr hpq, ?_⟩
      rintro rfl
      exact hab (hpq.2.symm.trans hpq.1)

private noncomputable def liftStep {V : Type u} [Fintype V]
    (G : SimpleGraph V) (x : V)
    (a b : {z : V // z ≠ x}) (hab : a ≠ b)
    (hxa : G.Adj x a.1) (hxb : G.Adj x b.1)
    {p q : {z : V // z ≠ x}} (hpq : (suppressAt G x a b).Adj p q) :
    G.Walk p.1 q.1 := by
  classical
  exact
    if hpa : p = a ∧ q = b then
      (SimpleGraph.Walk.cons hxa.symm
        (SimpleGraph.Walk.cons hxb SimpleGraph.Walk.nil)).copy
          (congrArg Subtype.val hpa.1.symm)
          (congrArg Subtype.val hpa.2.symm)
    else if hpb : p = b ∧ q = a then
      (SimpleGraph.Walk.cons hxb.symm
        (SimpleGraph.Walk.cons hxa SimpleGraph.Walk.nil)).copy
          (congrArg Subtype.val hpb.1.symm)
          (congrArg Subtype.val hpb.2.symm)
    else
      (show G.Adj p.1 q.1 from by
        rcases (suppressAt_adj_iff G x a b p q hab).mp hpq with
          hpq | hpq | hpq
        · exact hpq
        · exact (hpa hpq).elim
        · exact (hpb hpq).elim).toWalk

private noncomputable def liftWalk {V : Type u} [Fintype V]
    (G : SimpleGraph V) (x : V)
    (a b : {z : V // z ≠ x}) (hab : a ≠ b)
    (hxa : G.Adj x a.1) (hxb : G.Adj x b.1)
    {p q : {z : V // z ≠ x}} :
    (suppressAt G x a b).Walk p q → G.Walk p.1 q.1
  | .nil => .nil
  | .cons hpq w =>
      (liftStep G x a b hab hxa hxb hpq).append
        (liftWalk G x a b hab hxa hxb w)

private theorem liftStep_support {V : Type u} [Fintype V]
    (G : SimpleGraph V) (x : V)
    (a b : {z : V // z ≠ x}) (hab : a ≠ b)
    (hxa : G.Adj x a.1) (hxb : G.Adj x b.1)
    {p q : {z : V // z ≠ x}} (hpq : (suppressAt G x a b).Adj p q)
    {y : V} (hy : y ∈ (liftStep G x a b hab hxa hxb hpq).support) :
    y = x ∨ y = p.1 ∨ y = q.1 := by
  classical
  unfold liftStep at hy
  split at hy
  · simp only [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons] at hy
    obtain ⟨hpa, hqb⟩ := ‹p = a ∧ q = b›
    rcases hy with hy | hy | hy | hy
    · exact Or.inr (Or.inl
        (hy.trans (congrArg Subtype.val hpa).symm))
    · exact Or.inl hy
    · exact Or.inr (Or.inr
        (hy.trans (congrArg Subtype.val hqb).symm))
    · exact (List.not_mem_nil hy).elim
  · split at hy
    · simp only [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons] at hy
      obtain ⟨hpb, hqa⟩ := ‹p = b ∧ q = a›
      rcases hy with hy | hy | hy | hy
      · exact Or.inr (Or.inl
          (hy.trans (congrArg Subtype.val hpb).symm))
      · exact Or.inl hy
      · exact Or.inr (Or.inr
          (hy.trans (congrArg Subtype.val hqa).symm))
      · exact (List.not_mem_nil hy).elim
    · simp_all

private theorem liftStep_x_implies_special {V : Type u} [Fintype V]
    (G : SimpleGraph V) (x : V)
    (a b : {z : V // z ≠ x}) (hab : a ≠ b)
    (hxa : G.Adj x a.1) (hxb : G.Adj x b.1)
    {p q : {z : V // z ≠ x}} (hpq : (suppressAt G x a b).Adj p q)
    (hx : x ∈ (liftStep G x a b hab hxa hxb hpq).support) :
    (p = a ∧ q = b) ∨ (p = b ∧ q = a) := by
  classical
  unfold liftStep at hx
  split at hx
  · left
    assumption
  · split at hx
    · right
      assumption
    · exfalso
      simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      exact Or.elim hx
        (fun h => p.property h.symm)
        (fun h => q.property h.symm)

private theorem liftWalk_support {V : Type u} [Fintype V]
    (G : SimpleGraph V) (x : V)
    (a b : {z : V // z ≠ x}) (hab : a ≠ b)
    (hxa : G.Adj x a.1) (hxb : G.Adj x b.1)
    {p q : {z : V // z ≠ x}}
    (w : (suppressAt G x a b).Walk p q)
    {y : V} (hy : y ∈ (liftWalk G x a b hab hxa hxb w).support) :
    y = x ∨ ∃ z : {z : V // z ≠ x}, z ∈ w.support ∧ y = z.1 := by
  induction w with
  | @nil p =>
      simp only [liftWalk, SimpleGraph.Walk.support_nil,
        List.mem_singleton] at hy
      right
      exact ⟨p, by simp, hy⟩
  | @cons p r q hpr w ih =>
      simp only [liftWalk] at hy
      rw [SimpleGraph.Walk.mem_support_append_iff] at hy
      rcases hy with hy | hy
      · rcases liftStep_support G x a b hab hxa hxb hpr hy with
          rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr ⟨p, by simp, rfl⟩
        · exact Or.inr ⟨r, by simp, rfl⟩
      · rcases ih hy with rfl | ⟨z, hzw, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨z, by simp [hzw], rfl⟩

private theorem liftWalk_x_implies_edge {V : Type u} [Fintype V]
    (G : SimpleGraph V) (x : V)
    (a b : {z : V // z ≠ x}) (hab : a ≠ b)
    (hxa : G.Adj x a.1) (hxb : G.Adj x b.1)
    {p q : {z : V // z ≠ x}}
    (w : (suppressAt G x a b).Walk p q)
    (hx : x ∈ (liftWalk G x a b hab hxa hxb w).support) :
    s(a, b) ∈ w.edges := by
  induction w with
  | @nil p =>
      simp only [liftWalk, SimpleGraph.Walk.support_nil,
        List.mem_singleton] at hx
      exact (p.property hx.symm).elim
  | @cons p r q hpr w ih =>
      simp only [liftWalk] at hx
      rw [SimpleGraph.Walk.mem_support_append_iff] at hx
      rcases hx with hx | hx
      · rcases liftStep_x_implies_special G x a b hab hxa hxb hpr hx with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
      · simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr (ih hx)

private theorem eq_endpoint_of_support_not_interior
    {V : Type u} {G : SimpleGraph V} {p q y : V}
    (w : G.Walk p q) (hy : y ∈ w.support)
    (hnot : y ∉ walkInterior w) :
    y = p ∨ y = q := by
  by_contra h
  push Not at h
  exact hnot ⟨hy, h.1, h.2⟩

private theorem route_unique_of_common_edge
    {W : Type u} {V : Type v} {K : SimpleGraph W} {G : SimpleGraph V}
    (M : TopologicalModel K G)
    {i j k l : W} (hij : K.Adj i j) (hkl : K.Adj k l)
    {a b : V} (hab : a ≠ b)
    (heij : s(a, b) ∈ (M.route hij).edges)
    (hekl : s(a, b) ∈ (M.route hkl).edges) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  by_contra hne
  have hdis := M.route_interiors_disjoint hij hkl hne
  have hai : a ∈ (M.route hij).support :=
    (M.route hij).fst_mem_support_of_mem_edges heij
  have hbi : b ∈ (M.route hij).support :=
    (M.route hij).snd_mem_support_of_mem_edges heij
  have hak : a ∈ (M.route hkl).support :=
    (M.route hkl).fst_mem_support_of_mem_edges hekl
  have hbk : b ∈ (M.route hkl).support :=
    (M.route hkl).snd_mem_support_of_mem_edges hekl
  by_cases haint : a ∈ walkInterior (M.route hij)
  · by_cases hak0 : a = M.branch k
    · exact M.branch_avoids_interiors hij k (hak0 ▸ haint)
    · by_cases hal0 : a = M.branch l
      · exact M.branch_avoids_interiors hij l (hal0 ▸ haint)
      · have haint' : a ∈ walkInterior (M.route hkl) :=
          ⟨hak, hak0, hal0⟩
        exact Set.disjoint_left.mp hdis haint haint'
  · have haends :
        a = M.branch i ∨ a = M.branch j :=
      eq_endpoint_of_support_not_interior (M.route hij) hai haint
    by_cases hbint : b ∈ walkInterior (M.route hij)
    · by_cases hbk0 : b = M.branch k
      · exact M.branch_avoids_interiors hij k (hbk0 ▸ hbint)
      · by_cases hbl0 : b = M.branch l
        · exact M.branch_avoids_interiors hij l (hbl0 ▸ hbint)
        · have hbint' : b ∈ walkInterior (M.route hkl) :=
            ⟨hbk, hbk0, hbl0⟩
          exact Set.disjoint_left.mp hdis hbint hbint'
    · have hbends :
          b = M.branch i ∨ b = M.branch j :=
        eq_endpoint_of_support_not_interior (M.route hij) hbi hbint
      have hab_ends :
          (a = M.branch i ∧ b = M.branch j) ∨
          (a = M.branch j ∧ b = M.branch i) := by
        rcases haends with hai0 | haj0 <;>
          rcases hbends with hbi0 | hbj0
        · exact (hab (hai0.trans hbi0.symm)).elim
        · exact Or.inl ⟨hai0, hbj0⟩
        · exact Or.inr ⟨haj0, hbi0⟩
        · exact (hab (haj0.trans hbj0.symm)).elim
      by_cases haint' : a ∈ walkInterior (M.route hkl)
      · rcases hab_ends with ⟨hai0, -⟩ | ⟨haj0, -⟩
        · exact M.branch_avoids_interiors hkl i (hai0.symm ▸ haint')
        · exact M.branch_avoids_interiors hkl j (haj0.symm ▸ haint')
      · have haends' :
            a = M.branch k ∨ a = M.branch l :=
          eq_endpoint_of_support_not_interior (M.route hkl) hak haint'
        by_cases hbint' : b ∈ walkInterior (M.route hkl)
        · rcases hab_ends with ⟨-, hbj0⟩ | ⟨-, hbi0⟩
          · exact M.branch_avoids_interiors hkl j (hbj0.symm ▸ hbint')
          · exact M.branch_avoids_interiors hkl i (hbi0.symm ▸ hbint')
        · have hbends' :
              b = M.branch k ∨ b = M.branch l :=
            eq_endpoint_of_support_not_interior (M.route hkl) hbk hbint'
          rcases hab_ends with habij | habji <;>
            rcases haends' with hak0 | hal0 <;>
            rcases hbends' with hbk0 | hbl0
          · exact (hab (hak0.trans hbk0.symm)).elim
          · apply hne
            exact Or.inl ⟨M.branch.injective
              (habij.1.symm.trans hak0),
              M.branch.injective (habij.2.symm.trans hbl0)⟩
          · apply hne
            exact Or.inr ⟨M.branch.injective
              (habij.1.symm.trans hal0),
              M.branch.injective (habij.2.symm.trans hbk0)⟩
          · exact (hab (hal0.trans hbl0.symm)).elim
          · exact (hab (hak0.trans hbk0.symm)).elim
          · apply hne
            exact Or.inr ⟨M.branch.injective
              (habji.2.symm.trans hbl0),
              M.branch.injective (habji.1.symm.trans hak0)⟩
          · apply hne
            exact Or.inl ⟨M.branch.injective
              (habji.2.symm.trans hbk0),
              M.branch.injective (habji.1.symm.trans hal0)⟩
          · exact (hab (hal0.trans hbl0.symm)).elim

private noncomputable def liftTopologicalModel
    {W : Type u} {V : Type v} [Fintype V] [DecidableEq V]
    {K : SimpleGraph W} (G : SimpleGraph V) (x : V)
    (a b : {z : V // z ≠ x}) (hab : a ≠ b)
    (hxa : G.Adj x a.1) (hxb : G.Adj x b.1)
    (M : TopologicalModel K (suppressAt G x a b)) :
    TopologicalModel K G where
  branch :=
    M.branch.trans ⟨Subtype.val, Subtype.val_injective⟩
  route h :=
    (liftWalk G x a b hab hxa hxb (M.route h)).bypass
  route_isPath h :=
    SimpleGraph.Walk.bypass_isPath _
  branch_avoids_interiors := by
    intro i j hij w hw
    have hsupport_lift :
        ((M.branch w : {z : V // z ≠ x}) : V) ∈
          (liftWalk G x a b hab hxa hxb (M.route hij)).support :=
      SimpleGraph.Walk.support_bypass_subset _ hw.1
    rcases liftWalk_support G x a b hab hxa hxb
        (M.route hij) hsupport_lift with hxw | ⟨z, hz, hzw⟩
    · exact (M.branch w).property hxw
    · have hzw' : M.branch w = z :=
        Subtype.ext hzw
      subst z
      apply M.branch_avoids_interiors hij w
      refine ⟨hz, ?_, ?_⟩
      · intro hwi
        exact hw.2.1 (congrArg Subtype.val hwi)
      · intro hwj
        exact hw.2.2 (congrArg Subtype.val hwj)
  route_interiors_disjoint := by
    intro i j k l hij hkl hne
    rw [Set.disjoint_left]
    intro y hyij hykl
    have hyij_lift :
        y ∈ (liftWalk G x a b hab hxa hxb (M.route hij)).support :=
      SimpleGraph.Walk.support_bypass_subset _ hyij.1
    have hykl_lift :
        y ∈ (liftWalk G x a b hab hxa hxb (M.route hkl)).support :=
      SimpleGraph.Walk.support_bypass_subset _ hykl.1
    by_cases hyx : y = x
    · subst y
      have heij : s(a, b) ∈ (M.route hij).edges :=
        liftWalk_x_implies_edge G x a b hab hxa hxb
          (M.route hij) hyij_lift
      have hekl : s(a, b) ∈ (M.route hkl).edges :=
        liftWalk_x_implies_edge G x a b hab hxa hxb
          (M.route hkl) hykl_lift
      exact hne
        (route_unique_of_common_edge M hij hkl hab heij hekl)
    · rcases liftWalk_support G x a b hab hxa hxb
          (M.route hij) hyij_lift with hyx' | ⟨z, hz_ij, hyz⟩
      · exact hyx hyx'
      · rcases liftWalk_support G x a b hab hxa hxb
            (M.route hkl) hykl_lift with hyx' | ⟨z', hz_kl, hyz'⟩
        · exact hyx hyx'
        · have hzz' : z = z' :=
            Subtype.ext (hyz.symm.trans hyz')
          subst z'
          have hzint_ij : z ∈ walkInterior (M.route hij) := by
            refine ⟨hz_ij, ?_, ?_⟩
            · intro hzi
              exact hyij.2.1
                (hyz.trans (congrArg Subtype.val hzi))
            · intro hzj
              exact hyij.2.2
                (hyz.trans (congrArg Subtype.val hzj))
          have hzint_kl : z ∈ walkInterior (M.route hkl) := by
            refine ⟨hz_kl, ?_, ?_⟩
            · intro hzk
              exact hykl.2.1
                (hyz.trans (congrArg Subtype.val hzk))
            · intro hzl
              exact hykl.2.2
                (hyz.trans (congrArg Subtype.val hzl))
          exact
            Set.disjoint_left.mp
              (M.route_interiors_disjoint hij hkl hne)
              hzint_ij hzint_kl

private theorem hasTopologicalModel_suppressAt_imp
    {W : Type u} {V : Type v} [Fintype V]
    (K : SimpleGraph W) (G : SimpleGraph V) (x : V)
    (a b : {z : V // z ≠ x}) (hab : a ≠ b)
    (hxa : G.Adj x a.1) (hxb : G.Adj x b.1) :
    HasTopologicalModel K (suppressAt G x a b) →
      HasTopologicalModel K G := by
  classical
  rintro ⟨M⟩
  exact ⟨liftTopologicalModel G x a b hab hxa hxb M⟩

private theorem suppressAt_outerplanar
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (houter : IsOuterplanar G) (x : V)
    (a b : {z : V // z ≠ x}) (hab : a ≠ b)
    (hxa : G.Adj x a.1) (hxb : G.Adj x b.1) :
    IsOuterplanar (suppressAt G x a b) := by
  constructor
  · intro hmodel
    exact houter.1
      (hasTopologicalModel_suppressAt_imp
        (⊤ : SimpleGraph (Fin 4)) G x a b hab hxa hxb hmodel)
  · intro hmodel
    exact houter.2
      (hasTopologicalModel_suppressAt_imp
        (completeBipartiteGraph (Fin 2) (Fin 3))
        G x a b hab hxa hxb hmodel)

/-
The following first implementation of walk suppression is retained for
reference.  The final proof uses the generic suppression/model-lifting
helpers developed separately, which avoid this local recursive termination
proof.

private theorem exists_suppressed_walk {V : Type u} [Fintype V]
    (G : SimpleGraph V) (x a b : V)
    (hab : a ≠ b)
    (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hx_neighbors : ∀ ⦃z : V⦄, G.Adj x z → z = a ∨ z = b)
    {u v : V} (p : G.Walk u v) (hu : u ≠ x) (hv : v ≠ x) :
    ∃ q :
        (suppressAt G x
          ⟨a, G.ne_of_adj hxa.symm⟩
          ⟨b, G.ne_of_adj hxb.symm⟩).Walk
          ⟨u, hu⟩ ⟨v, hv⟩,
      ∀ z, z ∈ q.support → z.1 ∈ p.support := by
  classical
  let a' : {z : V // z ≠ x} := ⟨a, G.ne_of_adj hxa.symm⟩
  let b' : {z : V // z ≠ x} := ⟨b, G.ne_of_adj hxb.symm⟩
  let H : SimpleGraph {z : V // z ≠ x} := suppressAt G x a' b'
  let rec aux {u v : V} (p : G.Walk u v)
      (hu : u ≠ x) (hv : v ≠ x) :
      ∃ q : H.Walk ⟨u, hu⟩ ⟨v, hv⟩,
        ∀ z, z ∈ q.support → z.1 ∈ p.support := by
    cases p with
    | nil =>
        exact ⟨SimpleGraph.Walk.nil, by
          intro z hz
          have hz' : z = ⟨u, hu⟩ := by simpa using hz
          simpa [hz']⟩
    | @cons u w v huw p =>
        by_cases hw : w = x
        · subst w
          cases hp_eq : p with
          | nil => exact (hv rfl).elim
          | @cons _ z _ hxz p' =>
              have hz : z ≠ x := G.ne_of_adj hxz.symm
              obtain ⟨q, hq⟩ := aux p' hz hv
              by_cases huz : u = z
              · subst z
                refine ⟨q.copy (Subtype.ext rfl) rfl, ?_⟩
                intro y hy
                rw [SimpleGraph.Walk.support_copy] at hy
                have := hq y hy
                simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
                exact Or.inr (Or.inr this)
              · have hHuz : H.Adj ⟨u, hu⟩ ⟨z, hz⟩ := by
                  have hu_cases : u = a ∨ u = b :=
                    hx_neighbors huw.symm
                  have hz_cases : z = a ∨ z = b :=
                    hx_neighbors hxz
                  rw [show H = suppressAt G x a' b' by rfl]
                  apply (suppressAt_adj_iff G x a' b' _ _ (by
                    intro heq
                    exact hab (Subtype.ext_iff.mp heq))).2
                  rcases hu_cases with rfl | rfl <;>
                    rcases hz_cases with rfl | rfl
                  · exact False.elim (huz rfl)
                  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
                  · exact False.elim (huz rfl)
                refine ⟨SimpleGraph.Walk.cons hHuz q, ?_⟩
                intro y hy
                simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
                rcases hy with rfl | hy
                · simp
                · have := hq y hy
                  exact by simp [this]
        · have hw' : w ≠ x := hw
          obtain ⟨q, hq⟩ := aux p hw' hv
          have hHuw : H.Adj ⟨u, hu⟩ ⟨w, hw'⟩ := by
            rw [show H = suppressAt G x a' b' by rfl]
            exact (suppressAt_adj_iff G x a' b' _ _ (by
              intro heq
              exact hab (Subtype.ext_iff.mp heq))).2 (Or.inl huw)
          refine ⟨SimpleGraph.Walk.cons hHuw q, ?_⟩
          intro y hy
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
          rcases hy with rfl | hy
          · simp
          · exact by simp [hq y hy]
  termination_by p.length
  decreasing_by
    all_goals
      subst_vars
      simp_all
  simpa [H, a', b'] using aux p hu hv

private theorem suppressAt_twoConnected {V : Type u} [Fintype V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G)
    (hcard : 4 ≤ Nat.card V)
    (x a b : V)
    (hab : a ≠ b)
    (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hx_neighbors : ∀ ⦃z : V⦄, G.Adj x z → z = a ∨ z = b) :
    IsTwoConnected
      (suppressAt G x
        ⟨a, G.ne_of_adj hxa.symm⟩
        ⟨b, G.ne_of_adj hxb.symm⟩) := by
  classical
  let W : Type u := {z : V // z ≠ x}
  let a' : W := ⟨a, G.ne_of_adj hxa.symm⟩
  let b' : W := ⟨b, G.ne_of_adj hxb.symm⟩
  let H : SimpleGraph W := suppressAt G x a' b'
  have hcardV : Fintype.card V = Nat.card V := by
    simp [Nat.card_eq_fintype_card]
  have hcardW : Fintype.card W = Fintype.card V - 1 := by
    classical
    simpa [W, Set.ncard_eq_toFinset_card'] using
      Fintype.card_subtype_compl (fun z : V => z = x)
  have hthreeW : 3 ≤ Nat.card W := by
    rw [Nat.card_eq_fintype_card, hcardW, hcardV]
    omega
  refine ⟨hthreeW, ?_⟩
  intro y
  have hnontrivialW : Nontrivial W :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [← Nat.card_eq_fintype_card]
      omega)
  letI : Nontrivial W := hnontrivialW
  refine { preconnected := ?_, nonempty := ?_ }
  · intro r s
    let rG : {z : V // z ≠ y.1} :=
      ⟨r.1.1, by
        intro heq
        apply r.2
        exact Subtype.ext heq⟩
    let sG : {z : V // z ≠ y.1} :=
      ⟨s.1.1, by
        intro heq
        apply s.2
        exact Subtype.ext heq⟩
    obtain ⟨p, hp⟩ := (htwo.2 y.1).exists_isPath rG sG
    let inclusion : G.induce {z : V | z ≠ y.1} →g G :=
      { toFun := Subtype.val
        map_rel' := by
          intro z w hzw
          exact hzw }
    let pG : G.Walk r.1.1 s.1.1 := p.map inclusion
    have hpG_avoids_y :
        ∀ z : V, z ∈ pG.support → z ≠ y.1 := by
      intro z hz hzy
      rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨t, ht, htz⟩ := List.mem_map.mp hz
      have := t.2
      exact this (htz.trans hzy)
    obtain ⟨q, hq⟩ :=
      exists_suppressed_walk G x a b hab hxa hxb hx_neighbors
        pG r.1.2 s.1.2
    have hq_avoids_y :
        ∀ z : W, z ∈ q.support → z ≠ y := by
      intro z hz hzy
      apply hpG_avoids_y z.1 (hq z hz)
      exact congrArg Subtype.val hzy
    let q' := q.induce {z : W | z ≠ y} hq_avoids_y
    exact ⟨q'.copy (Subtype.ext rfl) (Subtype.ext rfl)⟩
  · obtain ⟨z, hzy⟩ := exists_ne y
    exact ⟨⟨z, hzy⟩⟩
-/

private theorem exists_suppressed_walk {V : Type u} [Fintype V]
    (G : SimpleGraph V) (x a b : V)
    (hab : a ≠ b)
    (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hx_neighbors : ∀ ⦃z : V⦄, G.Adj x z → z = a ∨ z = b)
    {p q : V} (w : G.Walk p q) (hp : p ≠ x) (hq : q ≠ x) :
    ∃ w' :
        (suppressAt G x
          ⟨a, G.ne_of_adj hxa.symm⟩
          ⟨b, G.ne_of_adj hxb.symm⟩).Walk
          ⟨p, hp⟩ ⟨q, hq⟩,
      ∀ z, z ∈ w'.support → z.1 ∈ w.support := by
  classical
  let a' : {z : V // z ≠ x} := ⟨a, G.ne_of_adj hxa.symm⟩
  let b' : {z : V // z ≠ x} := ⟨b, G.ne_of_adj hxb.symm⟩
  let H : SimpleGraph {z : V // z ≠ x} := suppressAt G x a' b'
  let rec aux {p q : V} (w : G.Walk p q)
      (hp : p ≠ x) (hq : q ≠ x) :
      ∃ w' : H.Walk ⟨p, hp⟩ ⟨q, hq⟩,
        ∀ z, z ∈ w'.support → z.1 ∈ w.support := by
    cases w with
    | nil =>
        exact ⟨SimpleGraph.Walk.nil, by
          intro z hz
          have hz' : z = ⟨p, hp⟩ := by simpa using hz
          simpa [hz']⟩
    | @cons p r q hpr w =>
        cases w with
        | nil =>
            have hHpr : H.Adj ⟨p, hp⟩ ⟨q, hq⟩ := by
              rw [show H = suppressAt G x a' b' by rfl]
              exact (suppressAt_adj_iff G x a' b' _ _ (by
                intro heq
                exact hab (Subtype.ext_iff.mp heq))).2 (Or.inl hpr)
            refine ⟨SimpleGraph.Walk.cons hHpr SimpleGraph.Walk.nil, ?_⟩
            intro y hy
            simp only [SimpleGraph.Walk.support_cons,
              SimpleGraph.Walk.support_nil, List.mem_cons] at hy ⊢
            rcases hy with hy | hy | hy
            · exact Or.inl (congrArg Subtype.val hy)
            · exact Or.inr (Or.inl (congrArg Subtype.val hy))
            · exact (List.not_mem_nil hy).elim
        | @cons _ s _ hxs w' =>
            by_cases hr : r = x
            · subst r
              have hs : s ≠ x := G.ne_of_adj hxs.symm
              obtain ⟨t, ht⟩ := aux w' hs hq
              by_cases hps : p = s
              · subst s
                refine ⟨t.copy (Subtype.ext rfl) rfl, ?_⟩
                intro y hy
                rw [SimpleGraph.Walk.support_copy] at hy
                have := ht y hy
                simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
                exact Or.inr (Or.inr this)
              · have hHps : H.Adj ⟨p, hp⟩ ⟨s, hs⟩ := by
                  have hp_cases : p = a ∨ p = b :=
                    hx_neighbors hpr.symm
                  have hs_cases : s = a ∨ s = b :=
                    hx_neighbors hxs
                  rw [show H = suppressAt G x a' b' by rfl]
                  apply (suppressAt_adj_iff G x a' b' _ _ (by
                    intro heq
                    exact hab (Subtype.ext_iff.mp heq))).2
                  rcases hp_cases with rfl | rfl <;>
                    rcases hs_cases with rfl | rfl
                  · exact False.elim (hps rfl)
                  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
                  · exact False.elim (hps rfl)
                refine ⟨SimpleGraph.Walk.cons hHps t, ?_⟩
                intro y hy
                simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
                rcases hy with rfl | hy
                · simp
                · have := ht y hy
                  exact by simp [this]
            · obtain ⟨t, ht⟩ :=
                aux (SimpleGraph.Walk.cons hxs w') hr hq
              have hHpr : H.Adj ⟨p, hp⟩ ⟨r, hr⟩ := by
                rw [show H = suppressAt G x a' b' by rfl]
                exact (suppressAt_adj_iff G x a' b' _ _ (by
                  intro heq
                  exact hab (Subtype.ext_iff.mp heq))).2 (Or.inl hpr)
              refine ⟨SimpleGraph.Walk.cons hHpr t, ?_⟩
              intro y hy
              simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
              rcases hy with rfl | hy
              · simp
              · simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
                exact Or.inr (by
                  simpa only [SimpleGraph.Walk.support_cons,
                    List.mem_cons] using ht y hy)
  termination_by w.length
  decreasing_by
    all_goals
      subst_vars
      simp_all
  simpa [H, a', b'] using aux w hp hq

private theorem suppressAt_twoConnected {V : Type u} [Fintype V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G)
    (hcard : 4 ≤ Nat.card V)
    (x a b : V)
    (hab : a ≠ b)
    (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hx_neighbors : ∀ ⦃z : V⦄, G.Adj x z → z = a ∨ z = b) :
    IsTwoConnected
      (suppressAt G x
        ⟨a, G.ne_of_adj hxa.symm⟩
        ⟨b, G.ne_of_adj hxb.symm⟩) := by
  classical
  let W : Type u := {z : V // z ≠ x}
  let a' : W := ⟨a, G.ne_of_adj hxa.symm⟩
  let b' : W := ⟨b, G.ne_of_adj hxb.symm⟩
  let H : SimpleGraph W := suppressAt G x a' b'
  have hcardV : Fintype.card V = Nat.card V := by
    simp [Nat.card_eq_fintype_card]
  have hcardW : Fintype.card W = Fintype.card V - 1 := by
    simpa [W, Set.ncard_eq_toFinset_card'] using
      Fintype.card_subtype_compl (fun z : V => z = x)
  have hthreeW : 3 ≤ Nat.card W := by
    rw [Nat.card_eq_fintype_card, hcardW, hcardV]
    omega
  refine ⟨hthreeW, ?_⟩
  intro y
  have hnontrivialW : Nontrivial W :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [← Nat.card_eq_fintype_card]
      omega)
  letI : Nontrivial W := hnontrivialW
  refine { preconnected := ?_, nonempty := ?_ }
  · intro r s
    let rG : {z : V // z ≠ y.1} :=
      ⟨r.1.1, by
        intro heq
        apply r.2
        exact Subtype.ext heq⟩
    let sG : {z : V // z ≠ y.1} :=
      ⟨s.1.1, by
        intro heq
        apply s.2
        exact Subtype.ext heq⟩
    obtain ⟨p, hp⟩ := (htwo.2 y.1).exists_isPath rG sG
    let inclusion : G.induce {z : V | z ≠ y.1} →g G :=
      { toFun := Subtype.val
        map_rel' := by
          intro z w hzw
          exact hzw }
    let pG : G.Walk r.1.1 s.1.1 := p.map inclusion
    have hpG_avoids_y :
        ∀ z : V, z ∈ pG.support → z ≠ y.1 := by
      intro z hz hzy
      rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨t, ht, htz⟩ := List.mem_map.mp hz
      exact t.2 (htz.trans hzy)
    obtain ⟨q, hq⟩ :=
      exists_suppressed_walk G x a b hab hxa hxb hx_neighbors
        pG r.1.2 s.1.2
    have hq_avoids_y :
        ∀ z : W, z ∈ q.support → z ≠ y := by
      intro z hz hzy
      apply hpG_avoids_y z.1 (hq z hz)
      exact congrArg Subtype.val hzy
    let q' := q.induce {z : W | z ≠ y} hq_avoids_y
    exact ⟨q'.copy (Subtype.ext rfl) (Subtype.ext rfl)⟩
  · obtain ⟨z, hzy⟩ := exists_ne y
    exact ⟨⟨z, hzy⟩⟩

private theorem twoConnected_connected {V : Type u} [Fintype V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G) :
    G.Connected := by
  classical
  have hcard : 2 < Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using htwo.1
  have hnonempty : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  refine { preconnected := ?_, nonempty := hnonempty }
  intro a b
  by_cases hab : a = b
  · simpa [hab]
  have hextra : ∃ z : V, z ≠ a ∧ z ≠ b := by
    by_contra! hall
    have huniv : (Finset.univ : Finset V) ⊆ {a, b} := by
      intro z hz
      by_cases hza : z = a
      · simp [hza]
      · have hzb : z = b := hall z hza
        simp [hzb]
    have hle : Fintype.card V ≤ ({a, b} : Finset V).card := by
      simpa using Finset.card_le_card huniv
    have hpair : ({a, b} : Finset V).card = 2 := by
      simp [hab]
    omega
  obtain ⟨z, hza, hzb⟩ := hextra
  let a' : {w : V // w ≠ z} := ⟨a, hza.symm⟩
  let b' : {w : V // w ≠ z} := ⟨b, hzb.symm⟩
  have hr : (G.induce {w : V | w ≠ z}).Reachable a' b' :=
    (htwo.2 z).preconnected a' b'
  let inclusion : G.induce {w : V | w ≠ z} →g G :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        exact hxy }
  exact hr.map inclusion

private theorem two_le_closedBallFinset_card {V : Type u} [Fintype V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G) (v : V) :
    2 ≤ (closedBallFinset G 1 v).card := by
  classical
  have hcard : 2 < Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using htwo.1
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hconn : G.Connected := twoConnected_connected G htwo
  have hdegree : 0 < G.degree v :=
    hconn.preconnected.degree_pos_of_nontrivial v
  obtain ⟨w, hvw⟩ : ∃ w : V, G.Adj v w := by
    simpa [SimpleGraph.degree_pos_iff_exists_adj] using hdegree
  have hv_ne_w : v ≠ w := G.ne_of_adj hvw
  have hv_mem : v ∈ closedBallFinset G 1 v := by
    simp only [closedBallFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  have hw_mem : w ∈ closedBallFinset G 1 v := by
    simp only [closedBallFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hvw.toWalk, by simp⟩
  exact (Finset.one_lt_card.mpr ⟨v, hv_mem, w, hw_mem, hv_ne_w⟩)

/--
Padding a positive no-clash map of width at most two to exact size two
preserves positivity and no-clash.
-/
private theorem pad_width_two {V : Type u} [Fintype V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G)
    (A : TeachingMap V 1)
    (hApositive : IsPositive G 1 A)
    (hAnoclash : IsNoClash G 1 A)
    (hAwidth : HasWidthAtMost A 2) :
    ∃ T : TeachingMap V 1,
      IsPositive G 1 T ∧
      IsNoClash G 1 T ∧
      ∀ v : V, (T v).card = 2 := by
  classical
  have extend (v : V) :
      ∃ t : Finset V,
        A v ⊆ t ∧
        t ⊆ closedBallFinset G 1 v ∧
        t.card = 2 := by
    have hA_ball : A v ⊆ closedBallFinset G 1 v := by
      intro x hx
      simp only [closedBallFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hApositive hx
    exact Finset.exists_subsuperset_card_eq hA_ball (hAwidth v)
      (two_le_closedBallFinset_card G htwo v)
  choose T hAT hTball hTcard using extend
  refine ⟨T, ?_, ?_, hTcard⟩
  · intro v x hx
    have hx' : x ∈ closedBallFinset G 1 v := hTball v hx
    simpa [closedBallFinset] using hx'
  · intro v w hvw
    obtain ⟨x, hxT, hxwitness⟩ := hAnoclash hvw
    exact ⟨x, hxT.elim (fun hx => Or.inl (hAT v hx))
      (fun hx => Or.inr (hAT w hx)), hxwitness⟩

private theorem closedBall_one_iff {V : Type u}
    (G : SimpleGraph V) (u v : V) :
    v ∈ closedBall G 1 u ↔ v = u ∨ G.Adj u v := by
  constructor
  · rintro ⟨p, hp⟩
    have hlength : p.length = 0 ∨ p.length = 1 := by omega
    rcases hlength with hzero | hone
    · exact Or.inl (p.eq_of_length_eq_zero hzero).symm
    · exact Or.inr (p.adj_of_length_eq_one hone)
  · rintro (rfl | huv)
    · exact ⟨SimpleGraph.Walk.nil, by simp⟩
    · exact ⟨huv.toWalk, by simp⟩

private theorem separates_symm {V : Type u} {G : SimpleGraph V} {k : ℕ}
    {T : TeachingMap V k} {u v : V} :
    Separates G k T u v → Separates G k T v u := by
  rintro ⟨z, hz, hw⟩
  exact ⟨z, hz.symm, hw.symm⟩

private theorem suppress_ball_transport_regular {V : Type u} [Fintype V]
    (G : SimpleGraph V) (x a b : V)
    (hab : a ≠ b)
    (hxa : G.Adj x a) (hxb : G.Adj x b)
    (y z : {w : V // w ≠ x})
    (hya : y.1 ≠ a) (hyb : y.1 ≠ b) :
    z ∈ closedBall
        (suppressAt G x
          ⟨a, G.ne_of_adj hxa.symm⟩
          ⟨b, G.ne_of_adj hxb.symm⟩) 1 y ↔
      z.1 ∈ closedBall G 1 y.1 := by
  rw [closedBall_one_iff, closedBall_one_iff]
  constructor
  · rintro (rfl | hyz)
    · exact Or.inl rfl
    · rcases (suppressAt_adj_iff G x
        ⟨a, G.ne_of_adj hxa.symm⟩
        ⟨b, G.ne_of_adj hxb.symm⟩ y z (by
          intro heq
          exact hab (Subtype.ext_iff.mp heq))).1 hyz with
        hyz | ⟨hya', -⟩ | ⟨hyb', -⟩
      · exact Or.inr hyz
      · exact False.elim (hya (congrArg Subtype.val hya'))
      · exact False.elim (hyb (congrArg Subtype.val hyb'))
  · rintro (hzy | hyz)
    · exact Or.inl (Subtype.ext hzy)
    · exact Or.inr <|
        (suppressAt_adj_iff G x
          ⟨a, G.ne_of_adj hxa.symm⟩
          ⟨b, G.ne_of_adj hxb.symm⟩ y z (by
            intro heq
            exact hab (Subtype.ext_iff.mp heq))).2 (Or.inl hyz)

private theorem x_not_mem_ball_regular {V : Type u}
    (G : SimpleGraph V) (x a b y : V)
    (hx_neighbors : ∀ ⦃z : V⦄, G.Adj x z → z = a ∨ z = b)
    (hyx : y ≠ x) (hya : y ≠ a) (hyb : y ≠ b) :
    x ∉ closedBall G 1 y := by
  rw [closedBall_one_iff]
  rintro (hxy | hyx_adj)
  · exact hyx hxy.symm
  · rcases hx_neighbors hyx_adj.symm with h | h
    · exact hya h
    · exact hyb h

private theorem exists_endpoint_repair {V : Type u} [Fintype V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G)
    (hcard : 4 ≤ Nat.card V)
    (x a b : V) (hab : a ≠ b)
    (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hx_neighbors : ∀ ⦃z : V⦄, G.Adj x z → z = a ∨ z = b) :
    ∃ c : V, c ∈ closedBall G 1 a ∧ c ∉ closedBall G 1 x := by
  classical
  have hextra : ∃ z : V, z ∉ ({x, a, b} : Finset V) := by
    by_contra! hall
    have huniv : (Finset.univ : Finset V) ⊆ {x, a, b} := by
      intro z hz
      exact hall z
    have hle : Fintype.card V ≤ ({x, a, b} : Finset V).card := by
      simpa using Finset.card_le_card huniv
    have hthree : ({x, a, b} : Finset V).card ≤ 3 :=
      Finset.card_le_three
    have hcard' : 4 ≤ Fintype.card V := by
      simpa [Nat.card_eq_fintype_card] using hcard
    omega
  obtain ⟨z, hz⟩ := hextra
  have hzx : z ≠ x := by
    intro h
    subst z
    exact hz (by simp)
  have hza : z ≠ a := by
    intro h
    subst z
    exact hz (by simp)
  have hzb : z ≠ b := by
    intro h
    subst z
    exact hz (by simp)
  by_contra! hnone
  let a' : {w : V // w ≠ b} := ⟨a, hab⟩
  let z' : {w : V // w ≠ b} := ⟨z, hzb⟩
  obtain ⟨p, hp⟩ := (htwo.2 b).exists_isPath a' z'
  have hane : a' ≠ z' := by
    intro h
    exact hza (congrArg Subtype.val h).symm
  obtain ⟨y, hay, q, hpform⟩ := p.exists_eq_cons_of_ne hane
  have hayG : G.Adj a y.1 := hay
  have hy_ball_a : y.1 ∈ closedBall G 1 a :=
    (closedBall_one_iff G a y.1).2 (Or.inr hayG)
  have hy_ball_x : y.1 ∈ closedBall G 1 x :=
    hnone y.1 hy_ball_a
  have hy_eq_x : y.1 = x := by
    rcases (closedBall_one_iff G x y.1).1 hy_ball_x with hyx | hxy
    · exact hyx
    · rcases hx_neighbors hxy with hya | hyb
      · exact False.elim (G.ne_of_adj hayG hya.symm)
      · exact False.elim (y.2 hyb)
  have hy_eq_x' : y = (⟨x, hxb.ne⟩ : {w : V // w ≠ b}) :=
    Subtype.ext hy_eq_x
  subst y
  have hqne : (⟨x, hxb.ne⟩ : {w : V // w ≠ b}) ≠ z' := by
    intro h
    exact hzx (congrArg Subtype.val h).symm
  obtain ⟨t, hxt, r, hqform⟩ := q.exists_eq_cons_of_ne hqne
  have hxtG : G.Adj x t.1 := hxt
  have ht_eq_a : t.1 = a := by
    rcases hx_neighbors hxtG with hta | htb
    · exact hta
    · exact False.elim (t.2 htb)
  have hpath_outer :
      (SimpleGraph.Walk.cons hay q).IsPath := by
    simpa [hpform] using hp
  have ha_not_q : a' ∉ q.support :=
    (SimpleGraph.Walk.cons_isPath_iff hay q).1 hpath_outer |>.2
  apply ha_not_q
  have ht_mem_q : t ∈ q.support := by
    rw [hqform]
    simp
  have ht_sub : t = a' := Subtype.ext ht_eq_a
  simpa [ht_sub] using ht_mem_q

private theorem exists_endpoint_repairs {V : Type u} [Fintype V]
    (G : SimpleGraph V) (houter : IsOuterplanar G)
    (htwo : IsTwoConnected G)
    (hcard : 5 ≤ Nat.card V)
    (x a b : V) (hab : a ≠ b)
    (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hx_neighbors : ∀ ⦃z : V⦄, G.Adj x z → z = a ∨ z = b) :
    ∃ cₐ cᵦ : V,
      cₐ ∈ closedBall G 1 a ∧
      cₐ ∉ closedBall G 1 x ∧
      cᵦ ∈ closedBall G 1 b ∧
      cᵦ ∉ closedBall G 1 x ∧
      (DistinctConcepts G 1 a b →
        cₐ ∉ closedBall G 1 b ∨ cᵦ ∉ closedBall G 1 a) := by
  classical
  have hfour : 4 ≤ Nat.card V := hcard.trans' (by omega)
  obtain ⟨cₐ, hcₐa, hcₐx⟩ :=
    exists_endpoint_repair G htwo hfour x a b hab hxa hxb hx_neighbors
  have hx_neighbors_swap :
      ∀ ⦃z : V⦄, G.Adj x z → z = b ∨ z = a := by
    intro z hxz
    exact (hx_neighbors hxz).symm
  obtain ⟨cᵦ, hcᵦb, hcᵦx⟩ :=
    exists_endpoint_repair G htwo hfour x b a hab.symm hxb hxa
      hx_neighbors_swap
  by_cases hsepA :
      ∃ c : V,
        (c ∈ closedBall G 1 a ∧ c ∉ closedBall G 1 x) ∧
        c ∉ closedBall G 1 b
  · obtain ⟨c, hc, hcb⟩ := hsepA
    exact ⟨c, cᵦ, hc.1, hc.2, hcᵦb, hcᵦx,
      fun _ => Or.inl hcb⟩
  by_cases hsepB :
      ∃ c : V,
        (c ∈ closedBall G 1 b ∧ c ∉ closedBall G 1 x) ∧
        c ∉ closedBall G 1 a
  · obtain ⟨c, hc, hca⟩ := hsepB
    exact ⟨cₐ, c, hcₐa, hcₐx, hc.1, hc.2,
      fun _ => Or.inr hca⟩
  have hallA (c : V)
      (hca : c ∈ closedBall G 1 a)
      (hcx : c ∉ closedBall G 1 x) :
      c ∈ closedBall G 1 b := by
    by_contra hcb
    exact hsepA ⟨c, ⟨hca, hcx⟩, hcb⟩
  have hallB (c : V)
      (hcb : c ∈ closedBall G 1 b)
      (hcx : c ∉ closedBall G 1 x) :
      c ∈ closedBall G 1 a := by
    by_contra hca
    exact hsepB ⟨c, ⟨hcb, hcx⟩, hca⟩
  have ha_ball_x : a ∈ closedBall G 1 x :=
    (closedBall_one_iff G x a).2 (Or.inr hxa)
  have hb_ball_x : b ∈ closedBall G 1 x :=
    (closedBall_one_iff G x b).2 (Or.inr hxb)
  have false_of_two_common_outside (c d : V)
      (hca : c ∈ closedBall G 1 a)
      (hcb : c ∈ closedBall G 1 b)
      (hcx : c ∉ closedBall G 1 x)
      (hda : d ∈ closedBall G 1 a)
      (hdb : d ∈ closedBall G 1 b)
      (hdx : d ∉ closedBall G 1 x)
      (hcd : c ≠ d) : False := by
    have hcx_ne : x ≠ c := by
      intro h
      apply hcx
      rw [← h]
      exact (closedBall_one_iff G x x).2 (Or.inl rfl)
    have hdx_ne : x ≠ d := by
      intro h
      apply hdx
      rw [← h]
      exact (closedBall_one_iff G x x).2 (Or.inl rfl)
    have hca_ne : c ≠ a := fun h => hcx (h ▸ ha_ball_x)
    have hcb_ne : c ≠ b := fun h => hcx (h ▸ hb_ball_x)
    have hda_ne : d ≠ a := fun h => hdx (h ▸ ha_ball_x)
    have hdb_ne : d ≠ b := fun h => hdx (h ▸ hb_ball_x)
    have hac : G.Adj a c :=
      ((closedBall_one_iff G a c).1 hca).resolve_left hca_ne
    have hbc : G.Adj b c :=
      ((closedBall_one_iff G b c).1 hcb).resolve_left hcb_ne
    have had : G.Adj a d :=
      ((closedBall_one_iff G a d).1 hda).resolve_left hda_ne
    have hbd : G.Adj b d :=
      ((closedBall_one_iff G b d).1 hdb).resolve_left hdb_ne
    exact false_of_k23_configuration houter a b x c d hab
      hcx_ne hdx_ne hcd hxa.symm hac had hxb.symm hbc hbd
  have hcₐb : cₐ ∈ closedBall G 1 b := hallA cₐ hcₐa hcₐx
  have hcᵦa : cᵦ ∈ closedBall G 1 a := hallB cᵦ hcᵦb hcᵦx
  have hc_eq : cᵦ = cₐ := by
    by_contra hne
    exact false_of_two_common_outside cₐ cᵦ hcₐa hcₐb hcₐx
      hcᵦa hcᵦb hcᵦx (fun h => hne h.symm)
  subst cᵦ
  have repairA_unique (c : V)
      (hca : c ∈ closedBall G 1 a)
      (hcx : c ∉ closedBall G 1 x) :
      c = cₐ := by
    by_contra hne
    exact false_of_two_common_outside c cₐ hca (hallA c hca hcx) hcx
      hcₐa hcₐb hcₐx hne
  have repairB_unique (c : V)
      (hcb : c ∈ closedBall G 1 b)
      (hcx : c ∉ closedBall G 1 x) :
      c = cₐ := by
    by_contra hne
    exact false_of_two_common_outside c cₐ (hallB c hcb hcx) hcb hcx
      hcₐa hcₐb hcₐx hne
  by_cases hab_adj : G.Adj a b
  · have hballs : closedBall G 1 a = closedBall G 1 b := by
      ext c
      constructor
      · intro hca
        by_cases hcx : c ∈ closedBall G 1 x
        · rcases (closedBall_one_iff G x c).1 hcx with hcx_eq | hxc
          · rw [hcx_eq]
            exact (closedBall_one_iff G b x).2 (Or.inr hxb.symm)
          · rcases hx_neighbors hxc with hca_eq | hcb_eq
            · rw [hca_eq]
              exact (closedBall_one_iff G b a).2 (Or.inr hab_adj.symm)
            · rw [hcb_eq]
              exact (closedBall_one_iff G b b).2 (Or.inl rfl)
        · rw [repairA_unique c hca hcx]
          exact hcₐb
      · intro hcb
        by_cases hcx : c ∈ closedBall G 1 x
        · rcases (closedBall_one_iff G x c).1 hcx with hcx_eq | hxc
          · rw [hcx_eq]
            exact (closedBall_one_iff G a x).2 (Or.inr hxa.symm)
          · rcases hx_neighbors hxc with hca_eq | hcb_eq
            · rw [hca_eq]
              exact (closedBall_one_iff G a a).2 (Or.inl rfl)
            · rw [hcb_eq]
              exact (closedBall_one_iff G a b).2 (Or.inr hab_adj)
        · rw [repairB_unique c hcb hcx]
          exact hcₐa
    exact ⟨cₐ, cₐ, hcₐa, hcₐx, hcₐb, hcₐx,
      fun hd => False.elim (hd hballs)⟩
  · have hcₐ_ne_x : cₐ ≠ x := by
      intro h
      subst cₐ
      exact hcₐx ((closedBall_one_iff G x x).2 (Or.inl rfl))
    have hcₐ_ne_a : cₐ ≠ a := fun h => hcₐx (h ▸ ha_ball_x)
    have hcₐ_ne_b : cₐ ≠ b := fun h => hcₐx (h ▸ hb_ball_x)
    have hextra :
        ∃ z : V, z ∉ ({x, a, b, cₐ} : Finset V) := by
      by_contra! hall
      have huniv : (Finset.univ : Finset V) ⊆ {x, a, b, cₐ} := by
        intro z hz
        exact hall z
      have hle : Fintype.card V ≤ ({x, a, b, cₐ} : Finset V).card := by
        simpa using Finset.card_le_card huniv
      have hfour' : ({x, a, b, cₐ} : Finset V).card ≤ 4 :=
        Finset.card_le_four
      have hcard' : 5 ≤ Fintype.card V := by
        simpa [Nat.card_eq_fintype_card] using hcard
      omega
    obtain ⟨z, hz⟩ := hextra
    have hzc : z ≠ cₐ := by
      intro h
      subst z
      exact hz (by simp)
    let a' : {w : V // w ≠ cₐ} := ⟨a, hcₐ_ne_a.symm⟩
    let x' : {w : V // w ≠ cₐ} := ⟨x, hcₐ_ne_x.symm⟩
    let b' : {w : V // w ≠ cₐ} := ⟨b, hcₐ_ne_b.symm⟩
    let z' : {w : V // w ≠ cₐ} := ⟨z, hzc⟩
    obtain ⟨p, hp⟩ := (htwo.2 cₐ).exists_isPath a' z'
    let S : Finset {w : V // w ≠ cₐ} := {a', x', b'}
    have hclosed :
        ∀ ⦃u v : {w : V // w ≠ cₐ}⦄,
          u ∈ S →
          (G.induce {w : V | w ≠ cₐ}).Adj u v →
          v ∈ S := by
      intro u v hu huv
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hu ⊢
      rcases hu with rfl | rfl | rfl
      · have hvx : v.1 = x := by
          by_contra hvx
          have hvb : v.1 ≠ b := by
            intro hvb
            exact hab_adj (hvb ▸ huv)
          have hv_ball_a : v.1 ∈ closedBall G 1 a :=
            (closedBall_one_iff G a v.1).2 (Or.inr huv)
          have hv_not_ball_x : v.1 ∉ closedBall G 1 x := by
            intro hv_ball_x
            rcases (closedBall_one_iff G x v.1).1 hv_ball_x with hvx' | hxv
            · exact hvx hvx'
            · rcases hx_neighbors hxv with hva | hvb'
              · exact G.ne_of_adj huv hva.symm
              · exact hvb hvb'
          exact v.2 (repairA_unique v.1 hv_ball_a hv_not_ball_x)
        exact Or.inr (Or.inl (Subtype.ext hvx))
      · rcases hx_neighbors huv with hva | hvb
        · exact Or.inl (Subtype.ext hva)
        · exact Or.inr (Or.inr (Subtype.ext hvb))
      · have hvx : v.1 = x := by
          by_contra hvx
          have hva : v.1 ≠ a := by
            intro hva
            exact hab_adj (hva ▸ huv.symm)
          have hv_ball_b : v.1 ∈ closedBall G 1 b :=
            (closedBall_one_iff G b v.1).2 (Or.inr huv)
          have hv_not_ball_x : v.1 ∉ closedBall G 1 x := by
            intro hv_ball_x
            rcases (closedBall_one_iff G x v.1).1 hv_ball_x with hvx' | hxv
            · exact hvx hvx'
            · rcases hx_neighbors hxv with hva' | hvb
              · exact hva hva'
              · exact G.ne_of_adj huv hvb.symm
          exact v.2 (repairB_unique v.1 hv_ball_b hv_not_ball_x)
        exact Or.inr (Or.inl (Subtype.ext hvx))
    have hzS : z' ∈ S :=
      walk_end_mem_of_closed S p (by simp [S]) hclosed
    have hzaxb : z = a ∨ z = x ∨ z = b := by
      simpa [S, a', x', b', z', Subtype.ext_iff] using hzS
    rcases hzaxb with hza | hzx | hzb
    · exact False.elim (hz (by simp [hza]))
    · exact False.elim (hz (by simp [hzx]))
    · exact False.elim (hz (by simp [hzb]))

private theorem base_four {V : Type u} [Fintype V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G)
    (hcard : Nat.card V = 4)
    (x a b : V) (hab : a ≠ b)
    (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hx_neighbors : ∀ ⦃z : V⦄, G.Adj x z → z = a ∨ z = b) :
    ∃ T : TeachingMap V 1,
      IsPositive G 1 T ∧
      IsNoClash G 1 T ∧
      ∀ y, (T y).card = 2 := by
  classical
  have htriple : ({x, a, b} : Finset V).card = 3 := by
    simp [hab, G.ne_of_adj hxa, G.ne_of_adj hxb]
  have hextra : ∃ c : V, c ∉ ({x, a, b} : Finset V) := by
    by_contra! hall
    have huniv : (Finset.univ : Finset V) ⊆ {x, a, b} := by
      intro c hc
      exact hall c
    have hle : Fintype.card V ≤ 3 := by
      simpa [htriple] using Finset.card_le_card huniv
    have hfour : Fintype.card V = 4 := by
      simpa [Nat.card_eq_fintype_card] using hcard
    omega
  obtain ⟨c, hc⟩ := hextra
  have hcx : c ≠ x := by
    intro h
    subst c
    exact hc (by simp)
  have hca : c ≠ a := by
    intro h
    subst c
    exact hc (by simp)
  have hcb : c ≠ b := by
    intro h
    subst c
    exact hc (by simp)
  have hquad : ({x, a, b, c} : Finset V).card = 4 := by
    have hset :
        ({x, a, b, c} : Finset V) = insert c {x, a, b} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hset, Finset.card_insert_of_notMem hc, htriple]
  have hall (z : V) : z = x ∨ z = a ∨ z = b ∨ z = c := by
    have hfin : ({x, a, b, c} : Finset V) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hquad]
      simpa [Nat.card_eq_fintype_card] using hcard.symm
    have : z ∈ ({x, a, b, c} : Finset V) := by rw [hfin]; simp
    simpa using this
  have hfour_le : 4 ≤ Nat.card V := by omega
  obtain ⟨dₐ, hdₐa, hdₐx⟩ :=
    exists_endpoint_repair G htwo hfour_le x a b hab hxa hxb hx_neighbors
  have hdₐ_eq : dₐ = c := by
    rcases hall dₐ with h | h | h | h
    · exfalso
      apply hdₐx
      rw [h]
      exact (closedBall_one_iff G x x).2 (Or.inl rfl)
    · exfalso
      apply hdₐx
      rw [h]
      exact (closedBall_one_iff G x a).2 (Or.inr hxa)
    · exfalso
      apply hdₐx
      rw [h]
      exact (closedBall_one_iff G x b).2 (Or.inr hxb)
    · exact h
  have hac : G.Adj a c := by
    rw [hdₐ_eq] at hdₐa
    exact ((closedBall_one_iff G a c).1 hdₐa).resolve_left hca
  have hx_neighbors_swap :
      ∀ ⦃z : V⦄, G.Adj x z → z = b ∨ z = a :=
    fun z hz => (hx_neighbors hz).symm
  obtain ⟨dᵦ, hdᵦb, hdᵦx⟩ :=
    exists_endpoint_repair G htwo hfour_le x b a hab.symm hxb hxa
      hx_neighbors_swap
  have hdᵦ_eq : dᵦ = c := by
    rcases hall dᵦ with h | h | h | h
    · exfalso
      apply hdᵦx
      rw [h]
      exact (closedBall_one_iff G x x).2 (Or.inl rfl)
    · exfalso
      apply hdᵦx
      rw [h]
      exact (closedBall_one_iff G x a).2 (Or.inr hxa)
    · exfalso
      apply hdᵦx
      rw [h]
      exact (closedBall_one_iff G x b).2 (Or.inr hxb)
    · exact h
  have hbc : G.Adj b c := by
    rw [hdᵦ_eq] at hdᵦb
    exact ((closedBall_one_iff G b c).1 hdᵦb).resolve_left hcb
  have hnxc : ¬ G.Adj x c := by
    intro h
    rcases hx_neighbors h with hca' | hcb'
    · exact hca hca'
    · exact hcb hcb'
  by_cases hab_adj : G.Adj a b
  · let T : TeachingMap V 1 := fun z =>
      if z = x then {x, a}
      else if z = a then {x, c}
      else if z = b then {x, c}
      else {a, c}
    have hT_x : T x = {x, a} := by simp [T]
    have hT_a : T a = {x, c} := by
      simp [T, G.ne_of_adj hxa, G.ne_of_adj hxa.symm]
    have hT_b : T b = {x, c} := by
      simp [T, G.ne_of_adj hxb, G.ne_of_adj hxb.symm, hab, hab.symm]
    have hT_c : T c = {a, c} := by
      simp [T, hcx, hca, hcb]
    have hball_a : closedBall G 1 a = Set.univ := by
      ext z
      simp only [Set.mem_univ, iff_true]
      rcases hall z with hz | hz | hz | hz <;> subst z
      · exact (closedBall_one_iff G a x).2 (Or.inr hxa.symm)
      · exact (closedBall_one_iff G a a).2 (Or.inl rfl)
      · exact (closedBall_one_iff G a b).2 (Or.inr hab_adj)
      · exact (closedBall_one_iff G a c).2 (Or.inr hac)
    have hball_b : closedBall G 1 b = Set.univ := by
      ext z
      simp only [Set.mem_univ, iff_true]
      rcases hall z with hz | hz | hz | hz <;> subst z
      · exact (closedBall_one_iff G b x).2 (Or.inr hxb.symm)
      · exact (closedBall_one_iff G b a).2 (Or.inr hab_adj.symm)
      · exact (closedBall_one_iff G b b).2 (Or.inl rfl)
      · exact (closedBall_one_iff G b c).2 (Or.inr hbc)
    have hc_not_ball_x : c ∉ closedBall G 1 x := by
      rw [← hdₐ_eq]
      exact hdₐx
    have hx_not_ball_c : x ∉ closedBall G 1 c := by
      rw [closedBall_one_iff]
      rintro (h | h)
      · exact hcx h.symm
      · exact hnxc h.symm
    have hsep_xa : Separates G 1 T x a :=
      ⟨c, Or.inr (by simp [hT_a]),
        Or.inr ⟨(closedBall_one_iff G a c).2 (Or.inr hac),
          hc_not_ball_x⟩⟩
    have hsep_xb : Separates G 1 T x b :=
      ⟨c, Or.inr (by simp [hT_b]),
        Or.inr ⟨(closedBall_one_iff G b c).2 (Or.inr hbc),
          hc_not_ball_x⟩⟩
    have hsep_xc : Separates G 1 T x c :=
      ⟨x, Or.inl (by simp [hT_x]),
        Or.inl ⟨(closedBall_one_iff G x x).2 (Or.inl rfl),
          hx_not_ball_c⟩⟩
    have hsep_ac : Separates G 1 T a c :=
      ⟨x, Or.inl (by simp [hT_a]),
        Or.inl ⟨(closedBall_one_iff G a x).2 (Or.inr hxa.symm),
          hx_not_ball_c⟩⟩
    have hsep_bc : Separates G 1 T b c :=
      ⟨x, Or.inl (by simp [hT_b]),
        Or.inl ⟨(closedBall_one_iff G b x).2 (Or.inr hxb.symm),
          hx_not_ball_c⟩⟩
    refine ⟨T, ?_, ?_, ?_⟩
    · intro u z hz
      rcases hall u with hu | hu | hu | hu
      · subst u
        rw [hT_x] at hz
        rcases Finset.mem_insert.mp hz with hzx | hz
        · rw [hzx]
          exact (closedBall_one_iff G x x).2 (Or.inl rfl)
        · have : z = a := by simpa using hz
          subst z
          exact (closedBall_one_iff G x a).2 (Or.inr hxa)
      · subst u
        rw [hT_a] at hz
        rcases Finset.mem_insert.mp hz with hzx | hz
        · rw [hzx]
          exact (closedBall_one_iff G a x).2 (Or.inr hxa.symm)
        · have : z = c := by simpa using hz
          subst z
          exact (closedBall_one_iff G a c).2 (Or.inr hac)
      · subst u
        rw [hT_b] at hz
        rcases Finset.mem_insert.mp hz with hzx | hz
        · rw [hzx]
          exact (closedBall_one_iff G b x).2 (Or.inr hxb.symm)
        · have : z = c := by simpa using hz
          subst z
          exact (closedBall_one_iff G b c).2 (Or.inr hbc)
      · subst u
        rw [hT_c] at hz
        rcases Finset.mem_insert.mp hz with hza | hz
        · rw [hza]
          exact (closedBall_one_iff G c a).2 (Or.inr hac.symm)
        · have : z = c := by simpa using hz
          subst z
          exact (closedBall_one_iff G c c).2 (Or.inl rfl)
    · intro u v huv
      rcases hall u with hu | hu | hu | hu
      · subst u
        rcases hall v with hv | hv | hv | hv
        · subst v; exact (huv rfl).elim
        · subst v; exact hsep_xa
        · subst v; exact hsep_xb
        · subst v; exact hsep_xc
      · subst u
        rcases hall v with hv | hv | hv | hv
        · subst v; exact separates_symm hsep_xa
        · subst v; exact (huv rfl).elim
        · subst v
          exact (huv (hball_a.trans hball_b.symm)).elim
        · subst v; exact hsep_ac
      · subst u
        rcases hall v with hv | hv | hv | hv
        · subst v; exact separates_symm hsep_xb
        · subst v
          exact (huv (hball_b.trans hball_a.symm)).elim
        · subst v; exact (huv rfl).elim
        · subst v; exact hsep_bc
      · subst u
        rcases hall v with hv | hv | hv | hv
        · subst v; exact separates_symm hsep_xc
        · subst v; exact separates_symm hsep_ac
        · subst v; exact separates_symm hsep_bc
        · subst v; exact (huv rfl).elim
    · intro z
      rcases hall z with hz | hz | hz | hz
      · subst z
        simp [hT_x, G.ne_of_adj hxa]
      · subst z
        simp [hT_a, hcx.symm]
      · subst z
        simp [hT_b, hcx.symm]
      · subst z
        simp [hT_c, hca.symm]
  · let T : TeachingMap V 1 := fun z =>
      if z = x then {x, a}
      else if z = a then {a, c}
      else if z = b then {x, c}
      else {b, c}
    have hT_x : T x = {x, a} := by simp [T]
    have hT_a : T a = {a, c} := by
      simp [T, G.ne_of_adj hxa, G.ne_of_adj hxa.symm]
    have hT_b : T b = {x, c} := by
      simp [T, G.ne_of_adj hxb, G.ne_of_adj hxb.symm, hab, hab.symm]
    have hT_c : T c = {b, c} := by
      simp [T, hcx, hca, hcb]
    have hba_non : ¬G.Adj b a := by
      intro h
      exact hab_adj h.symm
    have hcx_non : ¬G.Adj c x := by
      intro h
      exact hnxc h.symm
    have hc_not_ball_x : c ∉ closedBall G 1 x := by
      rw [← hdₐ_eq]
      exact hdₐx
    have hx_not_ball_c : x ∉ closedBall G 1 c := by
      rw [closedBall_one_iff]
      rintro (h | h)
      · exact hcx h.symm
      · exact hcx_non h
    have ha_not_ball_b : a ∉ closedBall G 1 b := by
      rw [closedBall_one_iff]
      rintro (h | h)
      · exact hab h
      · exact hba_non h
    have hb_not_ball_a : b ∉ closedBall G 1 a := by
      rw [closedBall_one_iff]
      rintro (h | h)
      · exact hab h.symm
      · exact hab_adj h
    have hsep_xa : Separates G 1 T x a :=
      ⟨c, Or.inr (by simp [hT_a]),
        Or.inr ⟨(closedBall_one_iff G a c).2 (Or.inr hac),
          hc_not_ball_x⟩⟩
    have hsep_xb : Separates G 1 T x b :=
      ⟨a, Or.inl (by simp [hT_x]),
        Or.inl ⟨(closedBall_one_iff G x a).2 (Or.inr hxa),
          ha_not_ball_b⟩⟩
    have hsep_xc : Separates G 1 T x c :=
      ⟨x, Or.inl (by simp [hT_x]),
        Or.inl ⟨(closedBall_one_iff G x x).2 (Or.inl rfl),
          hx_not_ball_c⟩⟩
    have hsep_ab : Separates G 1 T a b :=
      ⟨a, Or.inl (by simp [hT_a]),
        Or.inl ⟨(closedBall_one_iff G a a).2 (Or.inl rfl),
          ha_not_ball_b⟩⟩
    have hsep_ac : Separates G 1 T a c :=
      ⟨b, Or.inr (by simp [hT_c]),
        Or.inr ⟨(closedBall_one_iff G c b).2 (Or.inr hbc.symm),
          hb_not_ball_a⟩⟩
    have hsep_bc : Separates G 1 T b c :=
      ⟨x, Or.inl (by simp [hT_b]),
        Or.inl ⟨(closedBall_one_iff G b x).2 (Or.inr hxb.symm),
          hx_not_ball_c⟩⟩
    refine ⟨T, ?_, ?_, ?_⟩
    · intro u z hz
      rcases hall u with hu | hu | hu | hu
      · subst u
        rw [hT_x] at hz
        rcases Finset.mem_insert.mp hz with hzx | hz
        · rw [hzx]
          exact (closedBall_one_iff G x x).2 (Or.inl rfl)
        · have : z = a := by simpa using hz
          subst z
          exact (closedBall_one_iff G x a).2 (Or.inr hxa)
      · subst u
        rw [hT_a] at hz
        rcases Finset.mem_insert.mp hz with hza | hz
        · rw [hza]
          exact (closedBall_one_iff G a a).2 (Or.inl rfl)
        · have : z = c := by simpa using hz
          subst z
          exact (closedBall_one_iff G a c).2 (Or.inr hac)
      · subst u
        rw [hT_b] at hz
        rcases Finset.mem_insert.mp hz with hzx | hz
        · rw [hzx]
          exact (closedBall_one_iff G b x).2 (Or.inr hxb.symm)
        · have : z = c := by simpa using hz
          subst z
          exact (closedBall_one_iff G b c).2 (Or.inr hbc)
      · subst u
        rw [hT_c] at hz
        rcases Finset.mem_insert.mp hz with hzb | hz
        · rw [hzb]
          exact (closedBall_one_iff G c b).2 (Or.inr hbc.symm)
        · have : z = c := by simpa using hz
          subst z
          exact (closedBall_one_iff G c c).2 (Or.inl rfl)
    · intro u v huv
      rcases hall u with hu | hu | hu | hu
      · subst u
        rcases hall v with hv | hv | hv | hv
        · subst v; exact (huv rfl).elim
        · subst v; exact hsep_xa
        · subst v; exact hsep_xb
        · subst v; exact hsep_xc
      · subst u
        rcases hall v with hv | hv | hv | hv
        · subst v; exact separates_symm hsep_xa
        · subst v; exact (huv rfl).elim
        · subst v; exact hsep_ab
        · subst v; exact hsep_ac
      · subst u
        rcases hall v with hv | hv | hv | hv
        · subst v; exact separates_symm hsep_xb
        · subst v; exact separates_symm hsep_ab
        · subst v; exact (huv rfl).elim
        · subst v; exact hsep_bc
      · subst u
        rcases hall v with hv | hv | hv | hv
        · subst v; exact separates_symm hsep_xc
        · subst v; exact separates_symm hsep_ac
        · subst v; exact separates_symm hsep_bc
        · subst v; exact (huv rfl).elim
    · intro z
      rcases hall z with hz | hz | hz | hz
      · subst z
        simp [hT_x, G.ne_of_adj hxa]
      · subst z
        simp [hT_a, hca.symm]
      · subst z
        simp [hT_b, hcx.symm]
      · subst z
        simp [hT_c, hcb.symm]

private theorem base_three {V : Type u} [Fintype V]
    (G : SimpleGraph V) (htwo : IsTwoConnected G)
    (hcard : Nat.card V = 3)
    (x a b : V) (hab : a ≠ b)
    (hxa : G.Adj x a) (hxb : G.Adj x b) :
    ∃ T : TeachingMap V 1,
      IsPositive G 1 T ∧
      IsNoClash G 1 T ∧
      ∀ y, (T y).card = 2 := by
  classical
  have htriple : ({x, a, b} : Finset V).card = 3 := by
    simp [hab, G.ne_of_adj hxa, G.ne_of_adj hxb]
  have hall (z : V) : z = x ∨ z = a ∨ z = b := by
    have hfin : ({x, a, b} : Finset V) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [htriple]
      simpa [Nat.card_eq_fintype_card] using hcard.symm
    have : z ∈ ({x, a, b} : Finset V) := by rw [hfin]; simp
    simpa using this
  let a' : {z : V // z ≠ x} := ⟨a, G.ne_of_adj hxa.symm⟩
  let b' : {z : V // z ≠ x} := ⟨b, G.ne_of_adj hxb.symm⟩
  have hab' : a' ≠ b' := by
    intro h
    exact hab (congrArg Subtype.val h)
  obtain ⟨p, hp⟩ := (htwo.2 x).exists_isPath a' b'
  obtain ⟨y, hay, q, hpform⟩ := p.exists_eq_cons_of_ne hab'
  have hyb : y.1 = b := by
    rcases hall y.1 with hyx | hya | hyb
    · exact False.elim (y.2 hyx)
    · exact False.elim (G.ne_of_adj (show G.Adj a y.1 from hay) hya.symm)
    · exact hyb
  have hab_adj : G.Adj a b := by
    simpa [hyb] using (show G.Adj a y.1 from hay)
  have hball (u z : V) : z ∈ closedBall G 1 u := by
    rcases hall u with hu | hu | hu <;>
      rcases hall z with hz | hz | hz <;>
      subst u <;> subst z <;>
      simp [closedBall_one_iff, hxa, hxb, hab_adj,
        hxa.symm, hxb.symm, hab_adj.symm]
  let T : TeachingMap V 1 := fun _ => {x, a}
  refine ⟨T, ?_, ?_, ?_⟩
  · intro u z hz
    exact hball u z
  · intro u v huv
    exact False.elim (huv (Set.Subset.antisymm
      (fun _ _ => hball v _)
      (fun _ _ => hball u _)))
  · intro u
    simp [T, G.ne_of_adj hxa]

/--
The exact-two extension across a suppressed degree-two vertex.  The edge
between `a` and `b` may be newly added: only those two closed balls change in
the suppressed graph, and their teaching sets are replaced.
-/
private theorem extend_across_degree_two {V : Type u} [Fintype V]
    (G : SimpleGraph V) (x a b cₐ cᵦ : V)
    (hab : a ≠ b)
    (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hx_neighbors : ∀ ⦃z : V⦄, G.Adj x z → z = a ∨ z = b)
    (hcₐa : cₐ ∈ closedBall G 1 a)
    (hcₐx : cₐ ∉ closedBall G 1 x)
    (hcᵦb : cᵦ ∈ closedBall G 1 b)
    (hcᵦx : cᵦ ∉ closedBall G 1 x)
    (hendpoints :
      DistinctConcepts G 1 a b →
        cₐ ∉ closedBall G 1 b ∨ cᵦ ∉ closedBall G 1 a)
    (A : TeachingMap {z : V // z ≠ x} 1)
    (hApositive :
      IsPositive
        (suppressAt G x
          ⟨a, G.ne_of_adj hxa.symm⟩
          ⟨b, G.ne_of_adj hxb.symm⟩) 1 A)
    (hAnoclash :
      IsNoClash
        (suppressAt G x
          ⟨a, G.ne_of_adj hxa.symm⟩
          ⟨b, G.ne_of_adj hxb.symm⟩) 1 A)
    (hAcard : ∀ y, (A y).card = 2) :
    ∃ T : TeachingMap V 1,
      IsPositive G 1 T ∧
      IsNoClash G 1 T ∧
      ∀ y, (T y).card = 2 := by
  classical
  let valEmbedding : {z : V // z ≠ x} ↪ V := Function.Embedding.subtype _
  let T : TeachingMap V 1 := fun y =>
    if hyx : y = x then
      {x, a}
    else if hya : y = a then
      {x, cₐ}
    else if hyb : y = b then
      {x, cᵦ}
    else
      (A ⟨y, hyx⟩).map valEmbedding
  have hxa_ne : x ≠ a := G.ne_of_adj hxa
  have hxb_ne : x ≠ b := G.ne_of_adj hxb
  have hcₐ_ne_x : cₐ ≠ x := by
    intro h
    apply hcₐx
    rw [h]
    exact (closedBall_one_iff G x x).2 (Or.inl rfl)
  have hcᵦ_ne_x : cᵦ ≠ x := by
    intro h
    apply hcᵦx
    rw [h]
    exact (closedBall_one_iff G x x).2 (Or.inl rfl)
  have T_x : T x = {x, a} := by simp [T]
  have T_a : T a = {x, cₐ} := by simp [T, hxa_ne.symm]
  have T_b : T b = {x, cᵦ} := by simp [T, hxb_ne.symm, hab.symm]
  have T_regular (y : V) (hyx : y ≠ x) (hya : y ≠ a) (hyb : y ≠ b) :
      T y = (A ⟨y, hyx⟩).map valEmbedding := by
    simp [T, hyx, hya, hyb]
  refine ⟨T, ?_, ?_, ?_⟩
  · intro y z hz
    by_cases hyx : y = x
    · subst y
      rw [T_x] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz
      · subst z
        exact (closedBall_one_iff G x x).2 (Or.inl rfl)
      · subst z
        exact (closedBall_one_iff G x a).2 (Or.inr hxa)
    · by_cases hya : y = a
      · subst y
        rw [T_a] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz | hz
        · subst z
          exact (closedBall_one_iff G a x).2 (Or.inr hxa.symm)
        · subst z
          exact hcₐa
      · by_cases hyb : y = b
        · subst y
          rw [T_b] at hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with hz | hz
          · subst z
            exact (closedBall_one_iff G b x).2 (Or.inr hxb.symm)
          · subst z
            exact hcᵦb
        · rw [T_regular y hyx hya hyb] at hz
          obtain ⟨z', hz'A, rfl⟩ := Finset.mem_map.mp hz
          exact (suppress_ball_transport_regular G x a b hab hxa hxb
            ⟨y, hyx⟩ z' hya hyb).1 (hApositive hz'A)
  · intro y z hyz
    by_cases hyx : y = x
    · subst y
      have hzx : z ≠ x := by
        intro h
        subst z
        exact hyz rfl
      by_cases hza : z = a
      · subst z
        exact ⟨cₐ, Or.inr (by simp [T_a]), Or.inr ⟨hcₐa, hcₐx⟩⟩
      · by_cases hzb : z = b
        · subst z
          exact ⟨cᵦ, Or.inr (by simp [T_b]), Or.inr ⟨hcᵦb, hcᵦx⟩⟩
        · exact ⟨x, Or.inl (by simp [T_x]),
            Or.inl ⟨(closedBall_one_iff G x x).2 (Or.inl rfl),
              x_not_mem_ball_regular G x a b z hx_neighbors hzx hza hzb⟩⟩
    · by_cases hzx : z = x
      · subst z
        by_cases hya : y = a
        · subst y
          exact ⟨cₐ, Or.inl (by simp [T_a]), Or.inl ⟨hcₐa, hcₐx⟩⟩
        · by_cases hyb : y = b
          · subst y
            exact ⟨cᵦ, Or.inl (by simp [T_b]), Or.inl ⟨hcᵦb, hcᵦx⟩⟩
          · exact ⟨x, Or.inr (by simp [T_x]),
              Or.inr ⟨(closedBall_one_iff G x x).2 (Or.inl rfl),
                x_not_mem_ball_regular G x a b y hx_neighbors hyx hya hyb⟩⟩
      · by_cases hya : y = a
        · subst y
          by_cases hzb : z = b
          · subst z
            rcases hendpoints hyz with hcₐ | hcᵦ
            · exact ⟨cₐ, Or.inl (by simp [T_a]), Or.inl ⟨hcₐa, hcₐ⟩⟩
            · exact ⟨cᵦ, Or.inr (by simp [T_b]), Or.inr ⟨hcᵦb, hcᵦ⟩⟩
          · have hza : z ≠ a := by
              intro hza
              subst z
              exact hyz rfl
            exact ⟨x, Or.inl (by simp [T_a]),
              Or.inl ⟨(closedBall_one_iff G a x).2 (Or.inr hxa.symm),
                x_not_mem_ball_regular G x a b z hx_neighbors hzx
                  hza hzb⟩⟩
        · by_cases hyb : y = b
          · subst y
            by_cases hza : z = a
            · subst z
              rcases hendpoints (fun h => hyz h.symm) with hcₐ | hcᵦ
              · exact ⟨cₐ, Or.inr (by simp [T_a]), Or.inr ⟨hcₐa, hcₐ⟩⟩
              · exact ⟨cᵦ, Or.inl (by simp [T_b]), Or.inl ⟨hcᵦb, hcᵦ⟩⟩
            · have hzb : z ≠ b := by
                intro hzb
                subst z
                exact hyz rfl
              exact ⟨x, Or.inl (by simp [T_b]),
                Or.inl ⟨(closedBall_one_iff G b x).2 (Or.inr hxb.symm),
                  x_not_mem_ball_regular G x a b z hx_neighbors hzx hza
                    hzb⟩⟩
          · by_cases hza : z = a
            · subst z
              exact ⟨x, Or.inr (by simp [T_a]),
                Or.inr ⟨(closedBall_one_iff G a x).2 (Or.inr hxa.symm),
                  x_not_mem_ball_regular G x a b y hx_neighbors hyx hya hyb⟩⟩
            · by_cases hzb : z = b
              · subst z
                exact ⟨x, Or.inr (by simp [T_b]),
                  Or.inr ⟨(closedBall_one_iff G b x).2 (Or.inr hxb.symm),
                    x_not_mem_ball_regular G x a b y hx_neighbors hyx hya hyb⟩⟩
              · let y' : {w : V // w ≠ x} := ⟨y, hyx⟩
                let z' : {w : V // w ≠ x} := ⟨z, hzx⟩
                have hdistinct :
                    DistinctConcepts
                      (suppressAt G x
                        ⟨a, G.ne_of_adj hxa.symm⟩
                        ⟨b, G.ne_of_adj hxb.symm⟩) 1 y' z' := by
                  intro heq
                  apply hyz
                  ext w
                  by_cases hwx : w = x
                  · subst w
                    have hny :=
                      x_not_mem_ball_regular G x a b y hx_neighbors hyx hya hyb
                    have hnz :=
                      x_not_mem_ball_regular G x a b z hx_neighbors hzx hza hzb
                    simp [hny, hnz]
                  · let w' : {t : V // t ≠ x} := ⟨w, hwx⟩
                    exact (suppress_ball_transport_regular G x a b hab hxa hxb
                      y' w' hya hyb).symm.trans <|
                      (Set.ext_iff.mp heq w').trans <|
                      suppress_ball_transport_regular G x a b hab hxa hxb
                        z' w' hza hzb
                obtain ⟨w, hwA, hwwitness⟩ := hAnoclash hdistinct
                refine ⟨w.1, ?_, ?_⟩
                · rcases hwA with hwA | hwA
                  · exact Or.inl (by
                      rw [T_regular y hyx hya hyb]
                      exact Finset.mem_map.mpr ⟨w, hwA, rfl⟩)
                  · exact Or.inr (by
                      rw [T_regular z hzx hza hzb]
                      exact Finset.mem_map.mpr ⟨w, hwA, rfl⟩)
                · rcases hwwitness with ⟨hwy, hwz⟩ | ⟨hwz, hwy⟩
                  · exact Or.inl ⟨
                      (suppress_ball_transport_regular G x a b hab hxa hxb
                        y' w hya hyb).1 hwy,
                      fun hwG => hwz <|
                        (suppress_ball_transport_regular G x a b hab hxa hxb
                          z' w hza hzb).2 hwG⟩
                  · exact Or.inr ⟨
                      (suppress_ball_transport_regular G x a b hab hxa hxb
                        z' w hza hzb).1 hwz,
                      fun hwG => hwy <|
                        (suppress_ball_transport_regular G x a b hab hxa hxb
                          y' w hya hyb).2 hwG⟩
  · intro y
    by_cases hyx : y = x
    · subst y
      simp [T_x, hxa_ne]
    · by_cases hya : y = a
      · subst y
        simp [T_a, hcₐ_ne_x, hcₐ_ne_x.symm]
      · by_cases hyb : y = b
        · subst y
          simp [T_b, hcᵦ_ne_x, hcᵦ_ne_x.symm]
        · rw [T_regular y hyx hya hyb, Finset.card_map, hAcard]

private theorem natCard_survivors {V : Type u} [Fintype V] (x : V) :
    Nat.card {z : V // z ≠ x} = Nat.card V - 1 := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simpa [Set.ncard_eq_toFinset_card'] using
    Fintype.card_subtype_compl (fun z : V => z = x)

/--
The complete induction, factored through the sole structural reduction
interface.  The external graph theory supplies a degree-two vertex and the
two preservation statements for its suppression.
-/
private theorem exists_two_label_assignment_of_reduction
    (reduce :
      ∀ {W : Type u} [Fintype W]
        (H : SimpleGraph W),
        IsOuterplanar H →
        IsTwoConnected H →
        ∃ x a b : W,
          ∃ hxa : H.Adj x a,
          ∃ hxb : H.Adj x b,
          a ≠ b ∧
          (∀ ⦃z : W⦄, H.Adj x z → z = a ∨ z = b) ∧
          IsOuterplanar
            (suppressAt H x
              ⟨a, H.ne_of_adj hxa.symm⟩
              ⟨b, H.ne_of_adj hxb.symm⟩) ∧
          IsTwoConnected
            (suppressAt H x
              ⟨a, H.ne_of_adj hxa.symm⟩
              ⟨b, H.ne_of_adj hxb.symm⟩))
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (houter : IsOuterplanar G)
    (htwo : IsTwoConnected G) :
    ∃ T : TeachingMap V 1,
      IsPositive G 1 T ∧
      IsNoClash G 1 T ∧
      ∀ y, (T y).card = 2 := by
  classical
  let rec go {W : Type u} [Fintype W]
      (H : SimpleGraph W)
      (houterH : IsOuterplanar H)
      (htwoH : IsTwoConnected H) :
      ∃ T : TeachingMap W 1,
        IsPositive H 1 T ∧
        IsNoClash H 1 T ∧
        ∀ y, (T y).card = 2 := by
    obtain ⟨x, a, b, hxa, hxb, hab, hx_neighbors,
      houterS, htwoS⟩ := reduce H houterH htwoH
    by_cases hthree : Nat.card W = 3
    · exact base_three H htwoH hthree x a b hab hxa hxb
    by_cases hfour : Nat.card W = 4
    · exact base_four H htwoH hfour x a b hab hxa hxb hx_neighbors
    have hfive : 5 ≤ Nat.card W := by
      have := htwoH.1
      omega
    obtain ⟨cₐ, cᵦ, hcₐa, hcₐx, hcᵦb, hcᵦx, hendpoints⟩ :=
      exists_endpoint_repairs H houterH htwoH hfive x a b hab hxa hxb
        hx_neighbors
    let S : SimpleGraph {z : W // z ≠ x} :=
      suppressAt H x
        ⟨a, H.ne_of_adj hxa.symm⟩
        ⟨b, H.ne_of_adj hxb.symm⟩
    obtain ⟨A, hApositive, hAnoclash, hAcard⟩ :=
      go S (by simpa [S] using houterS) (by simpa [S] using htwoS)
    exact extend_across_degree_two H x a b cₐ cᵦ hab hxa hxb hx_neighbors
      hcₐa hcₐx hcᵦb hcᵦx hendpoints A
      (by simpa [S] using hApositive)
      (by simpa [S] using hAnoclash)
      hAcard
  termination_by Nat.card W
  decreasing_by
    rw [natCard_survivors]
    have := htwoH.1
    omega
  exact go G houter htwo

/--
Strong induction from the sole local structural input: every finite
two-connected outerplanar graph has a vertex of degree two.  The cardinality
three and four cases are discharged before suppression; this is necessary
because suppressing a three-vertex graph leaves only two vertices and hence
cannot preserve `IsTwoConnected`.
-/
theorem exists_two_label_assignment_of_degree_two
    (exists_degree_two :
      ∀ {W : Type u} [Fintype W] (H : SimpleGraph W)
        [DecidableRel H.Adj],
        IsOuterplanar H →
        IsTwoConnected H →
        ∃ x : W, H.degree x = 2)
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (houter : IsOuterplanar G)
    (htwo : IsTwoConnected G) :
    ∃ T : TeachingMap V 1,
      IsPositive G 1 T ∧
      IsNoClash G 1 T ∧
      ∀ y, (T y).card = 2 := by
  classical
  let rec go {W : Type u} [Fintype W]
      (H : SimpleGraph W)
      (houterH : IsOuterplanar H)
      (htwoH : IsTwoConnected H) :
      ∃ T : TeachingMap W 1,
        IsPositive H 1 T ∧
        IsNoClash H 1 T ∧
        ∀ y, (T y).card = 2 := by
    obtain ⟨x, hx⟩ := exists_degree_two H houterH htwoH
    obtain ⟨a, b, hab, hxa, hxb, hx_neighbors⟩ :=
      degree_two_neighbors H hx
    by_cases hthree : Nat.card W = 3
    · exact base_three H htwoH hthree x a b hab hxa hxb
    by_cases hfour : Nat.card W = 4
    · exact base_four H htwoH hfour x a b hab hxa hxb hx_neighbors
    have hfive : 5 ≤ Nat.card W := by
      have := htwoH.1
      omega
    obtain ⟨cₐ, cᵦ, hcₐa, hcₐx, hcᵦb, hcᵦx, hendpoints⟩ :=
      exists_endpoint_repairs H houterH htwoH hfive x a b hab hxa hxb
        hx_neighbors
    let a' : {z : W // z ≠ x} :=
      ⟨a, H.ne_of_adj hxa.symm⟩
    let b' : {z : W // z ≠ x} :=
      ⟨b, H.ne_of_adj hxb.symm⟩
    have hab' : a' ≠ b' := by
      intro heq
      exact hab (congrArg Subtype.val heq)
    let S : SimpleGraph {z : W // z ≠ x} :=
      suppressAt H x a' b'
    have houterS : IsOuterplanar S := by
      simpa only [S] using
        suppressAt_outerplanar H houterH x a' b' hab' hxa hxb
    have htwoS : IsTwoConnected S := by
      simpa only [S, a', b'] using
        suppressAt_twoConnected
          H htwoH (by omega) x a b hab hxa hxb hx_neighbors
    obtain ⟨A, hApositive, hAnoclash, hAcard⟩ :=
      go S houterS htwoS
    exact extend_across_degree_two H x a b cₐ cᵦ hab hxa hxb hx_neighbors
      hcₐa hcₐx hcᵦb hcᵦx hendpoints A
      (by simpa [S] using hApositive)
      (by simpa [S] using hAnoclash)
      hAcard
  termination_by Nat.card W
  decreasing_by
    rw [natCard_survivors]
    have := htwoH.1
    omega
  exact go G houter htwo

/--
---
conclusion: Lax16.OuterplanarBlockAssignment.exists_two_label_assignment
---
Every finite two-connected outerplanar graph has an exact two-label
positive no-clash teaching map.
-/
theorem exists_two_label_assignment
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (houter : IsOuterplanar G)
    (htwo : IsTwoConnected G) :
    ∃ T : TeachingMap V 1,
      IsPositive G 1 T ∧
      IsNoClash G 1 T ∧
      ∀ y, (T y).card = 2 :=
  exists_two_label_assignment_of_degree_two
    (fun H _ hHouter hHtwo =>
      Lax16ThetaFinal.exists_degree_two_outerplanar_twoConnected
        H hHouter hHtwo)
    G houter htwo

end Lax16Proofs.OuterplanarBlockAssignment
