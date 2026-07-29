import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Lax16.OuterplanarBound
import Lax16.OuterplanarBlockAssignment
import Lax16.ComponentReduction
import Lax16Proofs.OuterplanarBlockAssignment
import Lax16Proofs.PlanarToolbox

namespace Lax16Proofs.OuterplanarBound

open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u v

private def liftInducedModel {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V} {s : Set V}
    (M : TopologicalModel H (G.induce s)) :
    TopologicalModel H G where
  branch :=
    M.branch.trans (SimpleGraph.Embedding.induce s).toEmbedding
  route h :=
    Lax16Proofs.PlanarToolbox.liftInducedWalk (M.route h)
  route_isPath h := by
    apply SimpleGraph.Walk.map_isPath_of_injective
      Subtype.val_injective
    exact M.route_isPath h
  branch_avoids_interiors h w := by
    change (M.branch w).1 ∉
      walkInterior
        (Lax16Proofs.PlanarToolbox.liftInducedWalk (M.route h))
    rw [Lax16Proofs.PlanarToolbox.walkInterior_liftInducedWalk
      (M.route h)]
    rintro ⟨x, hx, hxeq⟩
    have hbranch : M.branch w = x := by
      exact Subtype.ext hxeq.symm
    subst x
    exact M.branch_avoids_interiors h w hx
  route_interiors_disjoint hab hcd hne := by
    have hi₁ :
        walkInterior
            (Lax16Proofs.PlanarToolbox.liftInducedWalk (M.route hab)) =
          Subtype.val '' walkInterior (M.route hab) :=
      Lax16Proofs.PlanarToolbox.walkInterior_liftInducedWalk _
    have hi₂ :
        walkInterior
            (Lax16Proofs.PlanarToolbox.liftInducedWalk (M.route hcd)) =
          Subtype.val '' walkInterior (M.route hcd) :=
      Lax16Proofs.PlanarToolbox.walkInterior_liftInducedWalk _
    change Disjoint
      (walkInterior
        (Lax16Proofs.PlanarToolbox.liftInducedWalk (M.route hab)))
      (walkInterior
        (Lax16Proofs.PlanarToolbox.liftInducedWalk (M.route hcd)))
    rw [hi₁, hi₂]
    exact
      Set.disjoint_image_of_injective Subtype.val_injective
        (M.route_interiors_disjoint hab hcd hne)

private theorem outerplanar_induce {V : Type u} {G : SimpleGraph V}
    (houter : IsOuterplanar G) (s : Set V) :
    IsOuterplanar (G.induce s) := by
  constructor
  · rintro ⟨M⟩
    exact houter.1 ⟨liftInducedModel M⟩
  · rintro ⟨M⟩
    exact houter.2 ⟨liftInducedModel M⟩

private theorem mem_closedBall_one_iff {V : Type u} {G : SimpleGraph V}
    {a b : V} :
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

private theorem closedBall_one_symm {V : Type u} {G : SimpleGraph V}
    {a b : V} :
    b ∈ closedBall G 1 a ↔ a ∈ closedBall G 1 b := by
  rw [mem_closedBall_one_iff, mem_closedBall_one_iff]
  constructor
  · rintro (rfl | hab)
    · exact Or.inl rfl
    · exact Or.inr hab.symm
  · rintro (rfl | hba)
    · exact Or.inl rfl
    · exact Or.inr hba.symm

private lemma walk_crosses_set {V : Type u} {G : SimpleGraph V}
    (s : Set V) {a b : V} (p : G.Walk a b)
    (ha : a ∈ s) (hb : b ∉ s) :
    ∃ x y : V, x ∈ s ∧ y ∉ s ∧ G.Adj x y := by
  induction p with
  | nil => exact (hb ha).elim
  | @cons a c b hac p ih =>
      by_cases hc : c ∈ s
      · exact ih hc hb
      · exact ⟨a, c, ha, hc, hac⟩

private def HasExactTwoMap {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ T : TeachingMap V 1,
    IsPositive G 1 T ∧
    IsNoClash G 1 T ∧
    ∀ x : V, (T x).card = 2

private theorem connected_outerplanar_exact_two
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (houter : IsOuterplanar G)
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V) :
    HasExactTwoMap G := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hn_two : n = 2
    · let T : TeachingMap V 1 := fun _ => Finset.univ
      have hadj_of_ne {a b : V} (hab : a ≠ b) : G.Adj a b := by
        exact (hconn.preconnected a b).elim_path fun p => by
          have hlt : p.1.length < 2 := by
            simpa [hn, hn_two] using p.2.length_lt
          have hpos : 0 < p.1.length := by
            exact Nat.pos_of_ne_zero fun hp =>
              hab (p.1.eq_of_length_eq_zero hp)
          have hone : p.1.length = 1 := by omega
          exact p.1.adj_of_length_eq_one hone
      refine ⟨T, ?_, ?_, ?_⟩
      · intro a x _
        exact mem_closedBall_one_iff.mpr
          (if h : x = a then Or.inl h else Or.inr (hadj_of_ne (Ne.symm h)))
      · intro a b hdifferent
        exfalso
        apply hdifferent
        ext x
        constructor <;> intro
        · exact mem_closedBall_one_iff.mpr
            (if h : x = b then Or.inl h else
              Or.inr (hadj_of_ne (Ne.symm h)))
        · exact mem_closedBall_one_iff.mpr
            (if h : x = a then Or.inl h else
              Or.inr (hadj_of_ne (Ne.symm h)))
      · intro
        simp [T, hn, hn_two]
    · have hn_three : 3 ≤ n := by omega
      by_cases htwo : IsTwoConnected G
      · exact
          Lax16Proofs.OuterplanarBlockAssignment.exists_two_label_assignment
            G houter htwo
      · have hcut :
            ∃ c : V, ¬(G.induce {w : V | w ≠ c}).Connected := by
          unfold IsTwoConnected at htwo
          push Not at htwo
          exact htwo (by simpa [hn] using hn_three)
        obtain ⟨c, hcut⟩ := hcut
        let D : SimpleGraph {w : V // w ≠ c} :=
          G.induce {w : V | w ≠ c}
        have hD_nonempty : Nonempty {w : V // w ≠ c} := by
          have hV_nontrivial : Nontrivial V :=
            Fintype.one_lt_card_iff_nontrivial.mp
              (by simpa [hn] using (show 1 < n by omega))
          exact ⟨⟨Classical.choose (exists_ne c),
            Classical.choose_spec (exists_ne c)⟩⟩
        have hD_not_preconnected : ¬D.Preconnected := by
          intro hpre
          exact hcut
            { preconnected := hpre
              nonempty := hD_nonempty }
        unfold SimpleGraph.Preconnected at hD_not_preconnected
        push Not at hD_not_preconnected
        obtain ⟨d₁, d₂, hd₁d₂⟩ := hD_not_preconnected
        let K₁ : D.ConnectedComponent := D.connectedComponentMk d₁
        let K₂ : D.ConnectedComponent := D.connectedComponentMk d₂
        have hK₁K₂ : K₁ ≠ K₂ := by
          intro h
          exact hd₁d₂ (SimpleGraph.ConnectedComponent.exact h)

        let BranchPred (K : D.ConnectedComponent) (x : V) : Prop :=
          x = c ∨ ∃ hx : x ≠ c, D.connectedComponentMk ⟨x, hx⟩ = K
        let Branch (K : D.ConnectedComponent) := {x : V // BranchPred K x}
        let H (K : D.ConnectedComponent) : SimpleGraph (Branch K) :=
          G.induce {x : V | BranchPred K x}

        have component_has_center_neighbor
            (K : D.ConnectedComponent) :
            ∃ q : {w : V // w ≠ c},
              D.connectedComponentMk q = K ∧ G.Adj c q.1 := by
          obtain ⟨k, hkK⟩ := K.nonempty_supp
          have hkc : (k : V) ≠ c := k.property
          obtain ⟨p⟩ := hconn.preconnected (k : V) c
          obtain ⟨x, y, hxK, hyK, hxy⟩ :=
            walk_crosses_set
              {z : V | ∃ hz : z ≠ c,
                D.connectedComponentMk ⟨z, hz⟩ = K}
              p ⟨k.property, hkK⟩ (by
                rintro ⟨hc, -⟩
                exact hc rfl)
          have hyc : y = c := by
            by_contra hyc
            obtain ⟨hxc, hxcomp⟩ := hxK
            have hDxy : D.Adj ⟨x, hxc⟩ ⟨y, hyc⟩ := hxy
            have hycomp :
                D.connectedComponentMk ⟨y, hyc⟩ = K := by
              calc
                D.connectedComponentMk ⟨y, hyc⟩ =
                    D.connectedComponentMk ⟨x, hxc⟩ :=
                  (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                    hDxy.symm)
                _ = K := hxcomp
            exact hyK ⟨hyc, hycomp⟩
          subst y
          obtain ⟨hxc, hxcomp⟩ := hxK
          exact ⟨⟨x, hxc⟩, hxcomp, hxy.symm⟩

        have branch_connected (K : D.ConnectedComponent) :
            (H K).Connected := by
          obtain ⟨q, hqK, hcq⟩ := component_has_center_neighbor K
          let center : Branch K := ⟨c, Or.inl rfl⟩
          let qB : Branch K := ⟨q.1, Or.inr ⟨q.property, hqK⟩⟩
          let fromComponent :
              K.toSimpleGraph →g H K :=
            { toFun := fun z =>
                ⟨z.1.1, Or.inr ⟨z.1.property, z.2⟩⟩
              map_rel' := fun h => h }
          have hcqH : (H K).Adj center qB := hcq
          refine
            { nonempty := ⟨center⟩
              preconnected := ?_ }
          intro a b
          have reachable_component
              {x y : Branch K}
              (hx : ∃ hxc : x.1 ≠ c,
                D.connectedComponentMk ⟨x.1, hxc⟩ = K)
              (hy : ∃ hyc : y.1 ≠ c,
                D.connectedComponentMk ⟨y.1, hyc⟩ = K) :
              (H K).Reachable x y := by
            obtain ⟨hxc, hxK⟩ := hx
            obtain ⟨hyc, hyK⟩ := hy
            let xK : K := ⟨⟨x.1, hxc⟩, hxK⟩
            let yK : K := ⟨⟨y.1, hyc⟩, hyK⟩
            have hreach :=
              (SimpleGraph.ConnectedComponent.connected_toSimpleGraph K).preconnected
                xK yK
            have hmapped := hreach.map fromComponent
            simpa [fromComponent, xK, yK] using hmapped
          rcases a.2 with ha | ha
          · have hac : a = center := Subtype.ext ha
            subst a
            rcases b.2 with hb | hb
            · have hbc : b = center := Subtype.ext hb
              subst b
              exact ⟨SimpleGraph.Walk.nil⟩
            · exact hcqH.reachable.trans
                (reachable_component
                  ⟨q.property, hqK⟩ hb)
          · rcases b.2 with hb | hb
            · have hbc : b = center := Subtype.ext hb
              subst b
              exact (hcqH.reachable.trans
                (reachable_component
                  ⟨q.property, hqK⟩ ha)).symm
            · exact reachable_component ha hb

        have branch_outer (K : D.ConnectedComponent) :
            IsOuterplanar (H K) :=
          outerplanar_induce houter _

        have branch_card_lt (K : D.ConnectedComponent) :
            Fintype.card (Branch K) < n := by
          have exists_outside :
              ∃ r : {w : V // w ≠ c},
                D.connectedComponentMk r ≠ K := by
            by_contra hnone
            push Not at hnone
            apply hcut
            exact
              { nonempty := hD_nonempty
                preconnected := by
                  intro x y
                  exact SimpleGraph.ConnectedComponent.exact
                    ((hnone x).trans (hnone y).symm) }
          obtain ⟨r, hr⟩ := exists_outside
          have hr_not : ¬ BranchPred K r.1 := by
            rintro (hrc | ⟨_, hrK⟩)
            · exact r.property hrc
            · exact hr hrK
          rw [← hn]
          exact Fintype.card_subtype_lt hr_not

        have branch_card_two (K : D.ConnectedComponent) :
            2 ≤ Fintype.card (Branch K) := by
          obtain ⟨q, hqK, hcq⟩ := component_has_center_neighbor K
          let center : Branch K := ⟨c, Or.inl rfl⟩
          let qB : Branch K := ⟨q.1, Or.inr ⟨q.property, hqK⟩⟩
          have hne : center ≠ qB := by
            intro h
            exact hcq.ne (congrArg Subtype.val h)
          exact Fintype.one_lt_card_iff_nontrivial.mpr
            ⟨⟨center, qB, hne⟩⟩

        have branch_assignment (K : D.ConnectedComponent) :
            HasExactTwoMap (H K) := by
          exact ih (Fintype.card (Branch K)) (branch_card_lt K)
            (H K) (branch_outer K)
            (branch_connected K) (branch_card_two K) rfl

        choose A hApositive hAnoclash hAcard using branch_assignment

        obtain ⟨q₁, hq₁K, hcq₁⟩ :=
          component_has_center_neighbor K₁
        obtain ⟨q₂, hq₂K, hcq₂⟩ :=
          component_has_center_neighbor K₂
        have hq₁q₂ : (q₁ : V) ≠ q₂ := by
          intro h
          apply hK₁K₂
          calc
            K₁ = D.connectedComponentMk q₁ := hq₁K.symm
            _ = D.connectedComponentMk q₂ := by
              congr 1
              exact Subtype.ext h
            _ = K₂ := hq₂K

        let cutLabels : Finset V := {q₁.1, q₂.1}
        have cutLabels_card : cutLabels.card = 2 := by
          simp [cutLabels, hq₁q₂]

        let localVertex (x : V) (hx : x ≠ c) :
            Branch (D.connectedComponentMk ⟨x, hx⟩) :=
          ⟨x, Or.inr ⟨hx, rfl⟩⟩
        let branchEmbedding (K : D.ConnectedComponent) :
            Branch K ↪ V :=
          ⟨Subtype.val, Subtype.val_injective⟩
        let T : TeachingMap V 1 := fun x =>
          if hx : x = c then cutLabels
          else
            (A (D.connectedComponentMk ⟨x, hx⟩)
              (localVertex x hx)).map
                (branchEmbedding (D.connectedComponentMk ⟨x, hx⟩))

        have T_center : T c = cutLabels := by
          simp [T]
        have T_noncenter {x : V} (hx : x ≠ c) :
            T x =
              (A (D.connectedComponentMk ⟨x, hx⟩)
                (localVertex x hx)).map
                  (branchEmbedding (D.connectedComponentMk ⟨x, hx⟩)) := by
          simp [T, hx]

        have branch_ball_to_ambient
            (K : D.ConnectedComponent) {a b : Branch K}
            (hab : b ∈ closedBall (H K) 1 a) :
            (b : V) ∈ closedBall G 1 (a : V) := by
          rw [mem_closedBall_one_iff] at hab ⊢
          rcases hab with rfl | hab
          · exact Or.inl rfl
          · exact Or.inr hab

        have ambient_ball_to_branch
            (K : D.ConnectedComponent) {a b : Branch K}
            (hab : (b : V) ∈ closedBall G 1 (a : V)) :
            b ∈ closedBall (H K) 1 a := by
          rw [mem_closedBall_one_iff] at hab ⊢
          rcases hab with hab | hab
          · exact Or.inl (Subtype.ext hab)
          · exact Or.inr hab

        have map_mem_transport
            (K L : D.ConnectedComponent) (hKL : K = L)
            (a z : Branch K) (b : Branch L)
            (hab : (a : V) = (b : V)) (hz : z ∈ A K a) :
            (z : V) ∈
              (A L b).map (branchEmbedding L) := by
          subst L
          have hab' : a = b := Subtype.ext hab
          subst b
          exact Finset.mem_map.mpr ⟨z, hz, rfl⟩

        have ball_mem_own_branch {x z : V} (hx : x ≠ c)
            (hz : z ∈ closedBall G 1 x) :
            BranchPred (D.connectedComponentMk ⟨x, hx⟩) z := by
          rw [mem_closedBall_one_iff] at hz
          rcases hz with rfl | hxz
          · exact Or.inr ⟨hx, rfl⟩
          · by_cases hzc : z = c
            · exact Or.inl hzc
            · refine Or.inr ⟨hzc, ?_⟩
              have hD : D.Adj ⟨z, hzc⟩ ⟨x, hx⟩ := hxz.symm
              exact
                SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                  hD

        have T_positive : IsPositive G 1 T := by
          intro x z hz
          by_cases hx : x = c
          · subst x
            rw [T_center] at hz
            simp only [cutLabels, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact mem_closedBall_one_iff.mpr (Or.inr hcq₁)
            · exact mem_closedBall_one_iff.mpr (Or.inr hcq₂)
          · rw [T_noncenter hx] at hz
            obtain ⟨zB, hzB, rfl⟩ := Finset.mem_map.mp hz
            exact branch_ball_to_ambient _
              (hApositive (D.connectedComponentMk ⟨x, hx⟩) hzB)

        have T_card (x : V) : (T x).card = 2 := by
          by_cases hx : x = c
          · subst x
            rw [T_center]
            exact cutLabels_card
          · rw [T_noncenter hx, Finset.card_map]
            exact hAcard (D.connectedComponentMk ⟨x, hx⟩)
              (localVertex x hx)

        refine ⟨T, T_positive, ?_, T_card⟩
        intro x y hdistinct
        have center_witness (z : V) (hz : z ≠ c) :
            ∃ q : V, q ∈ T c ∧ IsWitness G 1 q c z := by
          let Kz : D.ConnectedComponent :=
            D.connectedComponentMk ⟨z, hz⟩
          have use_label
              (q : {w : V // w ≠ c}) (Kq : D.ConnectedComponent)
              (hqK : D.connectedComponentMk q = Kq)
              (hcq : G.Adj c q.1) (hqcut : q.1 ∈ cutLabels)
              (hne : Kz ≠ Kq) :
              ∃ r : V, r ∈ T c ∧ IsWitness G 1 r c z := by
            refine ⟨q.1, ?_, ?_, ?_⟩
            · rw [T_center]
              exact hqcut
            · exact mem_closedBall_one_iff.mpr (Or.inr hcq)
            · intro hqz
              have hbranch := ball_mem_own_branch hz hqz
              rcases hbranch with hqc | ⟨_, hqcomp⟩
              · exact q.property hqc
              · apply hne
                exact hqcomp.symm.trans hqK
          by_cases hKz : Kz = K₁
          · apply use_label q₂ K₂ hq₂K hcq₂
              (by simp [cutLabels])
            intro hKzK₂
            exact hK₁K₂ (hKz.symm.trans hKzK₂)
          · apply use_label q₁ K₁ hq₁K hcq₁
              (by simp [cutLabels])
            exact hKz

        by_cases hxc : x = c
        · subst x
          have hyc : y ≠ c := by
            intro hyc
            subst y
            exact hdistinct rfl
          obtain ⟨q, hqT, hqwitness⟩ := center_witness y hyc
          exact ⟨q, Or.inl hqT, Or.inl hqwitness⟩
        · by_cases hyc : y = c
          · subst y
            obtain ⟨q, hqT, hqwitness⟩ := center_witness x hxc
            exact ⟨q, Or.inr hqT, Or.inr hqwitness⟩
          · let Kx : D.ConnectedComponent :=
              D.connectedComponentMk ⟨x, hxc⟩
            let Ky : D.ConnectedComponent :=
              D.connectedComponentMk ⟨y, hyc⟩
            by_cases hKxy : Kx = Ky
            · let xB : Branch Kx := localVertex x hxc
              let yB : Branch Kx :=
                ⟨y, Or.inr ⟨hyc, hKxy.symm⟩⟩
              have hlocalDistinct :
                  DistinctConcepts (H Kx) 1 xB yB := by
                intro hequal
                apply hdistinct
                ext z
                constructor
                · intro hzx
                  have hzpred := ball_mem_own_branch hxc hzx
                  let zB : Branch Kx := ⟨z, hzpred⟩
                  have hzlocal : zB ∈ closedBall (H Kx) 1 xB := by
                    exact ambient_ball_to_branch Kx hzx
                  rw [hequal] at hzlocal
                  exact branch_ball_to_ambient Kx hzlocal
                · intro hzy
                  have hzpred_y := ball_mem_own_branch hyc hzy
                  have hzpred_x : BranchPred Kx z := by
                    rcases hzpred_y with hzc | ⟨hzc, hzcomp⟩
                    · exact Or.inl hzc
                    · exact Or.inr ⟨hzc, hzcomp.trans hKxy.symm⟩
                  let zB : Branch Kx := ⟨z, hzpred_x⟩
                  have hzlocal : zB ∈ closedBall (H Kx) 1 yB := by
                    exact ambient_ball_to_branch Kx hzy
                  rw [← hequal] at hzlocal
                  exact branch_ball_to_ambient Kx hzlocal
              obtain ⟨zB, hzA, hzwitness⟩ :=
                hAnoclash Kx hlocalDistinct
              refine ⟨(zB : V), ?_, ?_⟩
              · rcases hzA with hzxA | hzyA
                · left
                  rw [T_noncenter hxc]
                  exact Finset.mem_map.mpr ⟨zB, hzxA, rfl⟩
                · right
                  rw [T_noncenter hyc]
                  exact map_mem_transport Kx Ky hKxy yB zB
                    (localVertex y hyc) rfl hzyA
              · rcases hzwitness with hzwitness | hzwitness
                · left
                  refine ⟨branch_ball_to_ambient Kx hzwitness.1, ?_⟩
                  intro hzy
                  exact hzwitness.2
                    (ambient_ball_to_branch Kx (a := yB) (b := zB) hzy)
                · right
                  refine ⟨branch_ball_to_ambient Kx hzwitness.1, ?_⟩
                  intro hzx
                  exact hzwitness.2
                    (ambient_ball_to_branch Kx (a := xB) (b := zB) hzx)
            · have hTcard_gt : 1 < (T x).card := by
                rw [T_card x]
                omega
              obtain ⟨z, hzT, hzc⟩ :=
                Finset.exists_mem_ne hTcard_gt c
              have hzx : z ∈ closedBall G 1 x := T_positive hzT
              have hzbranch_x := ball_mem_own_branch hxc hzx
              have hzcomp_x :
                  D.connectedComponentMk ⟨z, hzc⟩ = Kx := by
                rcases hzbranch_x with hzc' | ⟨hzne, hzcomp⟩
                · exact (hzc hzc').elim
                · simpa [Kx] using hzcomp
              have hzy : z ∉ closedBall G 1 y := by
                intro hzy
                have hzbranch_y := ball_mem_own_branch hyc hzy
                rcases hzbranch_y with hzc' | ⟨hzne, hzcomp_y⟩
                · exact hzc hzc'
                · apply hKxy
                  calc
                    Kx = D.connectedComponentMk ⟨z, hzc⟩ :=
                      hzcomp_x.symm
                    _ = D.connectedComponentMk ⟨z, hzne⟩ := by
                      congr
                    _ = Ky := by simpa [Ky] using hzcomp_y
              exact ⟨z, Or.inl hzT, Or.inl ⟨hzx, hzy⟩⟩

/--
---
conclusion: Lax16.OuterplanarBound.positiveNCTD_le_two
assumptions:
  - Lax16.ComponentReduction.combine_components
---
Decompose into connected components.  On each nontrivial component, recurse
at cut vertices; the two-connected leaves use the exact block assignment.
All recursive branch maps retain exact cardinality two, which separates
vertices belonging to different branches.
-/
theorem positiveNCTD_le_two {V : Type u} [Fintype V]
    (G : SimpleGraph V) (houter : IsOuterplanar G) :
    positiveNCTD G 1 ≤ 2 := by
  classical
  have hcomponents :
      ∀ C : G.ConnectedComponent,
        ∃ T : TeachingMap C 1,
          IsPositive C.toSimpleGraph 1 T ∧
          IsNoClash C.toSimpleGraph 1 T ∧
          HasWidthAtMost T 2 ∧
          HasNonemptySets T := by
    intro C
    have houterC : IsOuterplanar C.toSimpleGraph :=
      outerplanar_induce houter C.supp
    by_cases hsingle : Fintype.card C = 1
    · let T : TeachingMap C 1 := fun v => {v}
      refine ⟨T, ?_, ?_, ?_, ?_⟩
      · intro v x hx
        have hxv : x = v := by simpa [T] using hx
        subst x
        exact mem_closedBall_one_iff.mpr (Or.inl rfl)
      · intro v w hdistinct
        obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hsingle
        have hvw : v = w := (ha v).trans (ha w).symm
        subst w
        exact (hdistinct rfl).elim
      · intro v
        simp [T]
      · intro v
        exact ⟨v, by simp [T]⟩
    · let _ : Nonempty C := ⟨⟨C.out, C.out_eq⟩⟩
      have hcard_pos : 0 < Fintype.card C := Fintype.card_pos
      have hcard_two : 2 ≤ Fintype.card C := by omega
      obtain ⟨T, hpositive, hnoclash, hcard⟩ :=
        connected_outerplanar_exact_two C.toSimpleGraph houterC
          C.connected_toSimpleGraph hcard_two
      refine ⟨T, hpositive, hnoclash, ?_, ?_⟩
      · intro v
        rw [hcard v]
      · intro v
        exact Finset.card_pos.mp (by rw [hcard v]; omega)
  have hglobal : HasPositiveNCTDAtMost G 1 2 :=
    Lax16.ComponentReduction.combine_components G 2 hcomponents
  unfold positiveNCTD
  exact Nat.sInf_le hglobal

end Lax16Proofs.OuterplanarBound
