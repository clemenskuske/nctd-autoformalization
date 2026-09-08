import Lax60Proofs.OuterplanarThetaDirect
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Tactic.FinCases

namespace Lax60Proofs
namespace Lax60ThetaDirect

open Lax60.PlanarGraphs

universe u

set_option maxHeartbeats 2000000

private lemma snd_mem_walkInterior_of_two_le
    {V : Type u} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hlen : 2 ≤ p.length) :
    p.snd ∈ walkInterior p := by
  refine ⟨p.getVert_mem_support 1, ?_, ?_⟩
  · intro heq
    have hone : (1 : ℕ) = 0 :=
      (hp.getVert_eq_start_iff (i := 1) (by omega)).mp heq
    omega
  · intro heq
    have hone : (1 : ℕ) = p.length :=
      (hp.getVert_eq_end_iff (i := 1) (by omega)).mp heq
    omega

private lemma walkInterior_tail_subset
    {V : Type u} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hlen : 1 ≤ p.length) :
    walkInterior p.tail ⊆ walkInterior p := by
  have hnon : ¬p.Nil := by
    simpa [SimpleGraph.Walk.not_nil_iff_lt_length] using
      (show 0 < p.length by omega)
  have hsupp : p.tail.support = p.support.tail :=
    p.support_tail_of_not_nil hnon
  have hcons : a :: p.tail.support = p.support :=
    p.cons_support_tail hnon
  have hnodup : (a :: p.tail.support).Nodup := by
    rw [hcons]
    exact hp.support_nodup
  have ha_not_tail : a ∉ p.tail.support :=
    (List.nodup_cons.mp hnodup).1
  intro x hx
  refine ⟨?_, ?_, hx.2.2⟩
  · have hxtail : x ∈ p.tail.support := hx.1
    rw [hsupp] at hxtail
    exact List.mem_of_mem_tail hxtail
  · intro hxa
    apply ha_not_tail
    exact hxa ▸ hx.1

private lemma walkInterior_toWalk_eq_empty
    {V : Type u} {G : SimpleGraph V} {a b : V} (h : G.Adj a b) :
    walkInterior h.toWalk = ∅ := by
  ext z
  simp only [walkInterior, SimpleGraph.Adj.toWalk,
    SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
    List.mem_cons, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  aesop

namespace ThetaModel

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

private lemma route_length_pos (T : ThetaModel G) (i : Fin 3) :
    0 < (T.route i).length := by
  by_contra h
  have hz : (T.route i).length = 0 := by omega
  exact T.endpoints_ne ((T.route i).eq_of_length_eq_zero hz)

noncomputable def k23Branch (T : ThetaModel G)
    (hlen : ∀ i, 2 ≤ (T.route i).length) :
    (Fin 2 ⊕ Fin 3) ↪ V := by
  classical
  let leftBranch : Fin 2 → V := ![T.left, T.right]
  let branchFun : Fin 2 ⊕ Fin 3 → V :=
    Sum.elim leftBranch fun i => (T.route i).snd
  have hsnd (i : Fin 3) :
      (T.route i).snd ∈ walkInterior (T.route i) :=
    snd_mem_walkInterior_of_two_le (T.route i) (T.route_isPath i) (hlen i)
  refine { toFun := branchFun, inj' := ?_ }
  intro x y hxy
  cases x with
  | inl l =>
      cases y with
      | inl l' =>
          fin_cases l <;> fin_cases l' <;>
            simp only [branchFun, leftBranch, Sum.elim_inl,
              Matrix.cons_val_zero, Matrix.cons_val_one] at hxy ⊢
          · exact (T.endpoints_ne hxy).elim
          · exact (T.endpoints_ne hxy.symm).elim
      | inr j =>
          fin_cases l <;>
            simp only [branchFun, leftBranch, Sum.elim_inl, Sum.elim_inr,
              Matrix.cons_val_zero, Matrix.cons_val_one] at hxy
          · exact ((hsnd j).2.1 hxy.symm).elim
          · exact ((hsnd j).2.2 hxy.symm).elim
  | inr i =>
      cases y with
      | inl l =>
          fin_cases l <;>
            simp only [branchFun, leftBranch, Sum.elim_inl, Sum.elim_inr,
              Matrix.cons_val_zero, Matrix.cons_val_one] at hxy
          · exact ((hsnd i).2.1 hxy).elim
          · exact ((hsnd i).2.2 hxy).elim
      | inr j =>
          simp only [branchFun, Sum.elim_inr] at hxy
          congr 1
          by_contra hij
          exact Set.disjoint_left.mp (T.interiors_disjoint i j hij)
            (hsnd i) (hxy ▸ hsnd j)

lemma hasTopologicalModel_k23_of_two_le
    (T : ThetaModel G)
    (hlen : ∀ i, 2 ≤ (T.route i).length) :
    HasTopologicalModel
      (completeBipartiteGraph (Fin 2) (Fin 3)) G := by
  classical
  let branch := T.k23Branch hlen
  have hnonNil (i : Fin 3) : ¬(T.route i).Nil := by
    simpa [SimpleGraph.Walk.not_nil_iff_lt_length] using
      T.route_length_pos i
  have hadj (i : Fin 3) :
      G.Adj T.left (T.route i).snd :=
    SimpleGraph.Walk.adj_snd (hnonNil i)
  let ltr (l : Fin 2) (i : Fin 3) :
      G.Walk (branch (Sum.inl l)) (branch (Sum.inr i)) := by
    by_cases hl : l = 0
    · subst l
      simpa [branch, ThetaModel.k23Branch] using
        SimpleGraph.Adj.toWalk (hadj i)
    · have hl1 : l = 1 := by omega
      subst l
      simpa [branch, ThetaModel.k23Branch] using (T.route i).tail.reverse
  have hltrPath (l : Fin 2) (i : Fin 3) : (ltr l i).IsPath := by
    by_cases hl : l = 0
    · subst l
      simpa [ltr, branch, ThetaModel.k23Branch] using
        SimpleGraph.Walk.IsPath.of_adj (hadj i)
    · have hl1 : l = 1 := by omega
      subst l
      simpa [ltr, branch, ThetaModel.k23Branch] using
        (T.route_isPath i).tail.reverse
  have hltrInterior (l : Fin 2) (i : Fin 3) :
      walkInterior (ltr l i) ⊆ walkInterior (T.route i) := by
    by_cases hl : l = 0
    · subst l
      intro x hx
      have hempty :
          walkInterior (SimpleGraph.Adj.toWalk (hadj i)) = ∅ :=
        walkInterior_toWalk_eq_empty (hadj i)
      simpa [ltr, branch, ThetaModel.k23Branch, hempty] using hx
    · have hl1 : l = 1 := by omega
      subst l
      intro x hx
      apply walkInterior_tail_subset (T.route i) (T.route_isPath i)
        (Nat.succ_le_of_lt (T.route_length_pos i))
      have hx' :
          x ∈ (T.route i).tail.support ∧
            x ≠ T.right ∧ x ≠ (T.route i).snd := by
        simpa [ltr, branch, ThetaModel.k23Branch, walkInterior] using hx
      exact ⟨hx'.1, hx'.2.2, hx'.2.1⟩
  have hsnd (i : Fin 3) :
      (T.route i).snd ∈ walkInterior (T.route i) :=
    snd_mem_walkInterior_of_two_le (T.route i) (T.route_isPath i) (hlen i)
  have hbranchAvoid (l : Fin 2) (i : Fin 3)
      (w : Fin 2 ⊕ Fin 3) :
      branch w ∉ walkInterior (ltr l i) := by
    by_cases hl : l = 0
    · subst l
      rw [show walkInterior (ltr 0 i) = ∅ by
        simpa [ltr, branch, ThetaModel.k23Branch] using
          walkInterior_toWalk_eq_empty (hadj i)]
      simp
    · have hl1 : l = 1 := by omega
      subst l
      intro hw
      have hwOrig : branch w ∈ walkInterior (T.route i) :=
        hltrInterior 1 i hw
      cases w with
      | inl m =>
          fin_cases m
          · exact hwOrig.2.1 (by
              simp [branch, ThetaModel.k23Branch])
          · exact hw.2.1 (by
              simp [branch, ThetaModel.k23Branch])
      | inr j =>
          by_cases hij : i = j
          · subst j
            exact hw.2.2 (by
              simp [branch, ThetaModel.k23Branch])
          · exact Set.disjoint_left.mp (T.interiors_disjoint i j hij)
              hwOrig (by
                simpa [branch, ThetaModel.k23Branch] using hsnd j)
  have hltrDisjoint (l m : Fin 2) (i j : Fin 3)
      (hpairs : (l, i) ≠ (m, j)) :
      Disjoint (walkInterior (ltr l i)) (walkInterior (ltr m j)) := by
    by_cases hij : i = j
    · subst j
      have hlm : l ≠ m := by
        intro hlm
        exact hpairs (by simp [hlm])
      fin_cases l <;> fin_cases m <;>
        simp_all [ltr, branch, ThetaModel.k23Branch, walkInterior,
          Set.disjoint_left]
    · apply Set.disjoint_left.mpr
      intro x hxl hxm
      exact Set.disjoint_left.mp (T.interiors_disjoint i j hij)
        (hltrInterior l i hxl) (hltrInterior m j hxm)
  let route : ∀ {a b : Fin 2 ⊕ Fin 3},
      (completeBipartiteGraph (Fin 2) (Fin 3)).Adj a b →
      G.Walk (branch a) (branch b) := by
    intro a b hab
    cases a with
    | inl l =>
        cases b with
        | inl m => simp at hab
        | inr i => exact ltr l i
    | inr i =>
        cases b with
        | inl l => exact (ltr l i).reverse
        | inr j => simp at hab
  refine ⟨
    { branch := branch
      route := route
      route_isPath := ?_
      branch_avoids_interiors := ?_
      route_interiors_disjoint := ?_ }⟩
  · intro a b hab
    cases a with
    | inl l =>
        cases b with
        | inl m => simp at hab
        | inr i => exact hltrPath l i
    | inr i =>
        cases b with
        | inl l => exact (hltrPath l i).reverse
        | inr j => simp at hab
  · intro a b hab w
    cases a with
    | inl l =>
        cases b with
        | inl m => simp at hab
        | inr i => exact hbranchAvoid l i w
    | inr i =>
        cases b with
        | inl l =>
            simpa [route, walkInterior_reverse] using hbranchAvoid l i w
        | inr j => simp at hab
  · intro a b c d hab hcd hedges
    cases a with
    | inl l =>
        cases b with
        | inl m => simp at hab
        | inr i =>
            cases c with
            | inl n =>
                cases d with
                | inl o => simp at hcd
                | inr j =>
                    apply hltrDisjoint l n i j
                    intro hp
                    apply hedges
                    rcases Prod.ext_iff.mp hp with ⟨rfl, rfl⟩
                    simp
            | inr j =>
                cases d with
                | inl n =>
                    rw [walkInterior_reverse]
                    apply hltrDisjoint l n i j
                    intro hp
                    apply hedges
                    rcases Prod.ext_iff.mp hp with ⟨rfl, rfl⟩
                    simp
                | inr k => simp at hcd
    | inr i =>
        cases b with
        | inl l =>
            cases c with
            | inl n =>
                cases d with
                | inl o => simp at hcd
                | inr j =>
                    rw [walkInterior_reverse]
                    apply hltrDisjoint l n i j
                    intro hp
                    apply hedges
                    rcases Prod.ext_iff.mp hp with ⟨rfl, rfl⟩
                    simp
            | inr j =>
                cases d with
                | inl n =>
                    rw [walkInterior_reverse, walkInterior_reverse]
                    apply hltrDisjoint l n i j
                    intro hp
                    apply hedges
                    rcases Prod.ext_iff.mp hp with ⟨rfl, rfl⟩
                    simp
                | inr k => simp at hcd
        | inr j => simp at hab

lemma exists_length_one_of_no_k23
    (T : ThetaModel G)
    (hno :
      ¬ HasTopologicalModel
        (completeBipartiteGraph (Fin 2) (Fin 3)) G) :
    ∃ i : Fin 3, (T.route i).length = 1 := by
  by_contra hnone
  have hlen (i : Fin 3) : 2 ≤ (T.route i).length := by
    have hpositive : 0 < (T.route i).length := T.route_length_pos i
    have hneone : (T.route i).length ≠ 1 := by
      intro hone
      exact hnone ⟨i, hone⟩
    omega
  exact hno (T.hasTopologicalModel_k23_of_two_le hlen)

end ThetaModel

lemma exists_three_distinct_neighbors
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V)
    (hdegree : 3 ≤ G.degree v) :
    ∃ a b c : V,
      G.Adj v a ∧ G.Adj v b ∧ G.Adj v c ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have hcard : 2 < (G.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp hcard
  exact ⟨a, b, c, by simpa using ha, by simpa using hb, by simpa using hc,
    hab, hac, hbc⟩

lemma exists_path_avoiding_vertex
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (htwo : IsTwoConnected G)
    {a b deleted : V} (ha : a ≠ deleted) (hb : b ≠ deleted) :
    ∃ p : G.Walk a b, p.IsPath ∧ deleted ∉ p.support := by
  classical
  let a' : {w : V // w ≠ deleted} := ⟨a, ha⟩
  let b' : {w : V // w ≠ deleted} := ⟨b, hb⟩
  have hr :
      (G.induce {w : V | w ≠ deleted}).Reachable a' b' :=
    (htwo.2 deleted).preconnected a' b'
  let inclusion : G.induce {w : V | w ≠ deleted} →g G :=
    { toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        exact hxy }
  exact hr.elim_path fun q => by
    let p : G.Walk a b :=
      (q : (G.induce {w : V | w ≠ deleted}).Walk a' b').map inclusion
    refine ⟨p, ?_, ?_⟩
    · exact SimpleGraph.Walk.map_isPath_of_injective
        Subtype.val_injective q.prop
    · simp [p, inclusion]

lemma exists_initial_path_to_set
    {V : Type u} {G : SimpleGraph V} (S : Set V)
    {a b : V} (q : G.Walk a b) (hq : q.IsPath) (hb : b ∈ S) :
    ∃ t : V, t ∈ S ∧
      ∃ r : G.Walk a t,
        r.IsPath ∧
        (∀ x ∈ r.support, x ∈ S → x = t) ∧
        ∀ x ∈ r.support, x ∈ q.support := by
  induction q with
  | @nil a =>
      refine ⟨a, hb, .nil, by simp, ?_, ?_⟩
      · intro x hx _
        simpa using hx
      · intro x hx
        simpa using hx
  | @cons a c b hac q ih =>
      have hpath := (SimpleGraph.Walk.cons_isPath_iff hac q).mp hq
      by_cases ha : a ∈ S
      · refine ⟨a, ha, .nil, by simp, ?_, ?_⟩
        · intro x hx _
          simpa using hx
        · intro x hx
          simp at hx
          simp [hx]
      · obtain ⟨t, htS, r, hrpath, hrfirst, hrsub⟩ :=
          ih hpath.1 hb
        have ha_not_r : a ∉ r.support := by
          intro har
          exact hpath.2 (hrsub a har)
        refine ⟨t, htS, .cons hac r,
          (SimpleGraph.Walk.cons_isPath_iff hac r).mpr
            ⟨hrpath, ha_not_r⟩, ?_, ?_⟩
        · intro x hx hxS
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact (ha hxS).elim
          · exact hrfirst x hx hxS
        · intro x hx
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx ⊢
          exact hx.imp_right (hrsub x)

private lemma walkInterior_cons_subset_tail
    {V : Type u} {G : SimpleGraph V}
    {a b c x : V} (h : G.Adj a b) (p : G.Walk b c)
    (hx : x ∈ walkInterior (.cons h p)) :
    x ∈ p.support := by
  rcases hx with ⟨hxsupport, hxne, _⟩
  simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hxsupport
  exact hxsupport.resolve_left hxne

private lemma mem_support_takeUntil_and_dropUntil
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {a b t x : V} (p : G.Walk a b) (hp : p.IsPath)
    (ht : t ∈ p.support)
    (hxleft : x ∈ (p.takeUntil t ht).support)
    (hxright : x ∈ (p.dropUntil t ht).support) :
    x = t := by
  by_contra hxt
  have hpath : ((p.takeUntil t ht).append
      (p.dropUntil t ht)).IsPath := by simpa using hp
  exact hpath.ne_of_mem_support_of_append hxt
    hxleft hxright rfl

lemma exists_theta_of_degree_three
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (htwo : IsTwoConnected G) (v : V)
    (hdegree : 3 ≤ G.degree v) :
    ∃ T : ThetaModel G, T.left = v := by
  classical
  obtain ⟨a, b, c, hva, hvb, hvc, hab, hac, hbc⟩ :=
    exists_three_distinct_neighbors G v hdegree
  have hav : a ≠ v := hva.ne.symm
  have hbv : b ≠ v := hvb.ne.symm
  have hcv : c ≠ v := hvc.ne.symm
  obtain ⟨p, hp, hvp⟩ :=
    exists_path_avoiding_vertex G htwo hav hbv
  obtain ⟨q, hq, hvq⟩ :=
    exists_path_avoiding_vertex G htwo hcv hav
  let S : Set V := {x | x ∈ p.support}
  have haS : a ∈ S := p.start_mem_support
  obtain ⟨t, htS, r, hr, hrfirst, hrsubq⟩ :=
    exists_initial_path_to_set S q hq haS
  have htp : t ∈ p.support := htS
  let pa : G.Walk a t := p.takeUntil t htp
  let pb : G.Walk b t := (p.dropUntil t htp).reverse
  let pc : G.Walk c t := r
  let arm0 : G.Walk v t := .cons hva pa
  let arm1 : G.Walk v t := .cons hvb pb
  let arm2 : G.Walk v t := .cons hvc pc
  have hvt : v ≠ t := by
    intro h
    apply hvp
    rw [h]
    exact htp
  have hpa : pa.IsPath := hp.takeUntil htp
  have hpb : pb.IsPath := by
    simpa [pb] using (hp.dropUntil htp).reverse
  have hpc : pc.IsPath := hr
  have hvpa : v ∉ pa.support := by
    intro hv
    exact hvp (p.support_takeUntil_subset_support htp hv)
  have hvpb : v ∉ pb.support := by
    intro hv
    apply hvp
    apply p.support_dropUntil_subset htp
    simpa [pb] using hv
  have hvpc : v ∉ pc.support := by
    intro hv
    exact hvq (hrsubq v hv)
  have harm0 : arm0.IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff hva pa).mpr ⟨hpa, hvpa⟩
  have harm1 : arm1.IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff hvb pb).mpr ⟨hpb, hvpb⟩
  have harm2 : arm2.IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff hvc pc).mpr ⟨hpc, hvpc⟩
  let routes : Fin 3 → G.Walk v t := ![arm0, arm1, arm2]
  refine ⟨
    { left := v
      right := t
      endpoints_ne := hvt
      route := routes
      route_isPath := ?_
      route_snd_injective := ?_
      interiors_disjoint := ?_ },
    rfl⟩
  · intro i
    fin_cases i <;> simp [routes, harm0, harm1, harm2]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [routes, arm0, arm1, arm2,
        SimpleGraph.Walk.snd_cons, hab, hac, hbc]
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    fin_cases i <;> fin_cases j <;>
      simp only [routes, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two] at hxi hxj
    all_goals
      try { exact (hij rfl).elim }
    · have hxpa := walkInterior_cons_subset_tail hva pa hxi
      have hxpb := walkInterior_cons_subset_tail hvb pb hxj
      have hxdrop : x ∈ (p.dropUntil t htp).support := by
        simpa [pb] using hxpb
      exact hxi.2.2
        (mem_support_takeUntil_and_dropUntil p hp htp hxpa hxdrop)
    · have hxpa := walkInterior_cons_subset_tail hva pa hxi
      have hxpc := walkInterior_cons_subset_tail hvc pc hxj
      have hxp : x ∈ p.support :=
        p.support_takeUntil_subset_support htp hxpa
      exact hxi.2.2 (hrfirst x hxpc hxp)
    · have hxpb := walkInterior_cons_subset_tail hvb pb hxi
      have hxpa := walkInterior_cons_subset_tail hva pa hxj
      have hxdrop : x ∈ (p.dropUntil t htp).support := by
        simpa [pb] using hxpb
      exact hxi.2.2
        (mem_support_takeUntil_and_dropUntil p hp htp hxpa hxdrop)
    · have hxpb := walkInterior_cons_subset_tail hvb pb hxi
      have hxpc := walkInterior_cons_subset_tail hvc pc hxj
      have hxdrop : x ∈ (p.dropUntil t htp).support := by
        simpa [pb] using hxpb
      have hxp : x ∈ p.support :=
        p.support_dropUntil_subset htp hxdrop
      exact hxi.2.2 (hrfirst x hxpc hxp)
    · have hxpc := walkInterior_cons_subset_tail hvc pc hxi
      have hxpa := walkInterior_cons_subset_tail hva pa hxj
      have hxp : x ∈ p.support :=
        p.support_takeUntil_subset_support htp hxpa
      exact hxi.2.2 (hrfirst x hxpc hxp)
    · have hxpc := walkInterior_cons_subset_tail hvc pc hxi
      have hxpb := walkInterior_cons_subset_tail hvb pb hxj
      have hxdrop : x ∈ (p.dropUntil t htp).support := by
        simpa [pb] using hxpb
      have hxp : x ∈ p.support :=
        p.support_dropUntil_subset htp hxdrop
      exact hxi.2.2 (hrfirst x hxpc hxp)

end Lax60ThetaDirect
end Lax60Proofs
