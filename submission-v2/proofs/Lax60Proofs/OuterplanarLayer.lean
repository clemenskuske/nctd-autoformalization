import Lax60.OuterplanarLayer
import Lax60.OuterplanarBound
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases

namespace Lax60Proofs.OuterplanarLayer

open Lax60.OuterplanarLayer
open Lax60.PlanarGraphs
open Lax60.TeachingMaps

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

private theorem false_of_k4_configuration
    {V : Type u} {G : SimpleGraph V} (houter : IsOuterplanar G)
    (f : Fin 4 → V) (hf : Function.Injective f)
    (hadj : ∀ i j : Fin 4, i ≠ j → G.Adj (f i) (f j)) :
    False := by
  apply houter.1
  let hom : (⊤ : SimpleGraph (Fin 4)) →g G :=
    { toFun := f
      map_rel' := by
        intro i j hij
        exact hadj i j (by simpa using hij) }
  exact ⟨directTopologicalModel hom hf⟩

/--
---
conclusion: Lax60.OuterplanarLayer.exists_outerplanar_layer_assignment
assumptions:
  - Lax60.OuterplanarBound.positiveNCTD_le_two
---
Transport a width-two positive map from the induced outerplanar layer.
Classes of induced closed twins have size at most three.  A two-element
class needs at most one ambient repair label per vertex; on a three-element
class, use the self-label and at most two repair labels.  Such a triple is an
isolated component by the forbidden-`K₄` condition.
-/
theorem exists_outerplanar_layer_assignment {V : Type u} [Fintype V]
    (G : SimpleGraph V) (v₀ : V) (U : Finset V)
    (hneighbors : ∀ w ∈ U, G.Adj v₀ w)
    (houter : IsOuterplanar (G.induce (↑U : Set V))) :
    ∃ S : TeachingMap V 1,
      IsLayerAssignment G U S ∧
      (∀ w : V, w ∈ U →
        (anchoredTeaching v₀ S w).card ≤ 4 ∧
        ∀ y ∈ anchoredTeaching v₀ S w, y ∈ closedBall G 1 w) ∧
      ∀ w : V, w ∈ U → ∀ x : V, x ∉ closedBall G 1 v₀ →
        ∃ y ∈ anchoredTeaching v₀ S w, y ∉ closedBall G 1 x := by
  classical
  let W : Set V := ↑U
  let H : SimpleGraph W := G.induce W
  letI : Fintype W := Fintype.ofFinite W
  have houterH : IsOuterplanar H := by
    simpa [H, W] using houter

  have ball_one_iff_ambient (a b : V) :
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

  have ball_one_iff_induced (a b : W) :
      b ∈ closedBall H 1 a ↔ b = a ∨ H.Adj a b := by
    constructor
    · rintro ⟨p, hp⟩
      have hlength : p.length = 0 ∨ p.length = 1 := by omega
      rcases hlength with hzero | hone
      · exact Or.inl (p.eq_of_length_eq_zero hzero).symm
      · exact Or.inr (p.adj_of_length_eq_one hone)
    · rintro (rfl | hab)
      · exact ⟨SimpleGraph.Walk.nil, by simp⟩
      · exact ⟨hab.toWalk, by simp⟩

  have ball_transport (a b : W) :
      b ∈ closedBall H 1 a ↔
        (b : V) ∈ closedBall G 1 (a : V) := by
    rw [ball_one_iff_induced, ball_one_iff_ambient]
    simp [H]

  let fullMap : TeachingMap W 1 := fun a =>
    closedBallFinset H 1 a
  have full_positive : IsPositive H 1 fullMap := by
    intro a x hx
    simpa [fullMap, closedBallFinset] using hx
  have full_noclash : IsNoClash H 1 fullMap := by
    intro a b hdifferent
    by_cases hsubset : closedBall H 1 a ⊆ closedBall H 1 b
    · have hnreverse : ¬ closedBall H 1 b ⊆ closedBall H 1 a := by
        intro hreverse
        exact hdifferent (Set.Subset.antisymm hsubset hreverse)
      obtain ⟨x, hxb, hxa⟩ := Set.not_subset.mp hnreverse
      exact ⟨x, Or.inr (by
        simpa [fullMap, closedBallFinset] using hxb),
        Or.inr ⟨hxb, hxa⟩⟩
    · obtain ⟨x, hxa, hxb⟩ := Set.not_subset.mp hsubset
      exact ⟨x, Or.inl (by
        simpa [fullMap, closedBallFinset] using hxa),
        Or.inl ⟨hxa, hxb⟩⟩
  have full_width :
      HasWidthAtMost fullMap (Fintype.card W) := by
    intro a
    exact Finset.card_le_univ _
  have bound_nonempty :
      {d : ℕ | HasPositiveNCTDAtMost H 1 d}.Nonempty := by
    exact ⟨Fintype.card W, fullMap, full_positive, full_noclash, full_width⟩
  have minimum_realized :
      HasPositiveNCTDAtMost H 1 (positiveNCTD H 1) := by
    exact Nat.sInf_mem bound_nonempty
  obtain ⟨A, hApositive, hAnoclash, hAwidthMin⟩ :=
    minimum_realized
  have hbound :
      positiveNCTD H 1 ≤ 2 :=
    Lax60.OuterplanarBound.positiveNCTD_le_two H houterH
  have hAwidth : HasWidthAtMost A 2 := by
    intro a
    exact (hAwidthMin a).trans hbound

  let twins (a : W) : Finset W :=
    Finset.univ.filter fun b => closedBall H 1 b = closedBall H 1 a
  have self_mem_twins (a : W) : a ∈ twins a := by
    simp [twins]

  have twins_card_le_three (a : W) : (twins a).card ≤ 3 := by
    by_contra hnot
    have hfour : 4 ≤ (twins a).card := by omega
    have hfin :
        Fintype.card (Fin 4) ≤ (twins a).card := by simpa using hfour
    obtain ⟨f, hfmem⟩ :=
      Function.Embedding.exists_of_card_le_finset hfin
    have hftwin (i : Fin 4) :
        closedBall H 1 (f i) = closedBall H 1 a := by
      have hi := hfmem ⟨i, rfl⟩
      simpa [twins] using hi
    apply false_of_k4_configuration houterH f f.injective
    intro i j hij
    have hselfj : f j ∈ closedBall H 1 (f j) :=
      (ball_one_iff_induced (f j) (f j)).2 (Or.inl rfl)
    have hjballi : f j ∈ closedBall H 1 (f i) := by
      rw [hftwin i, ← hftwin j]
      exact hselfj
    rcases (ball_one_iff_induced (f i) (f j)).1 hjballi with heq | hadj
    · exact False.elim (hij (f.injective heq.symm))
    · exact hadj

  have twin_symm {a b : W} (h : b ∈ twins a) : a ∈ twins b := by
    have heq : closedBall H 1 b = closedBall H 1 a := by
      simpa [twins] using h
    simp [twins, heq]

  have twin_trans {a b c : W}
      (hab : b ∈ twins a) (hbc : c ∈ twins b) :
      c ∈ twins a := by
    have hab' : closedBall H 1 b = closedBall H 1 a := by
      simpa [twins] using hab
    have hbc' : closedBall H 1 c = closedBall H 1 b := by
      simpa [twins] using hbc
    simp [twins, hbc'.trans hab']

  have twins_eq_of_mem {a b : W} (h : b ∈ twins a) :
      twins b = twins a := by
    ext c
    constructor
    · exact fun hc => twin_trans h hc
    · intro hc
      exact twin_trans (twin_symm h) hc

  have twins_three_isolated (a b : W)
      (hcard : (twins a).card = 3)
      (hbnot : b ∉ twins a) :
      ¬ H.Adj a b := by
    intro hab
    obtain ⟨c₁, c₂, c₃, hc₁c₂, hc₁c₃, hc₂c₃, htwins⟩ :=
      Finset.card_eq_three.mp hcard
    have hc₁mem : c₁ ∈ twins a := by rw [htwins]; simp
    have hc₂mem : c₂ ∈ twins a := by rw [htwins]; simp
    have hc₃mem : c₃ ∈ twins a := by rw [htwins]; simp
    have hc₁eq : closedBall H 1 c₁ = closedBall H 1 a := by
      simpa [twins] using hc₁mem
    have hc₂eq : closedBall H 1 c₂ = closedBall H 1 a := by
      simpa [twins] using hc₂mem
    have hc₃eq : closedBall H 1 c₃ = closedBall H 1 a := by
      simpa [twins] using hc₃mem
    have hbballa : b ∈ closedBall H 1 a :=
      (ball_one_iff_induced a b).2 (Or.inr hab)
    have hc₁b : H.Adj c₁ b := by
      have hball : b ∈ closedBall H 1 c₁ := hc₁eq.symm ▸ hbballa
      rcases (ball_one_iff_induced c₁ b).1 hball with heq | hadj
      · subst b
        exact False.elim (hbnot hc₁mem)
      · exact hadj
    have hc₂b : H.Adj c₂ b := by
      have hball : b ∈ closedBall H 1 c₂ := hc₂eq.symm ▸ hbballa
      rcases (ball_one_iff_induced c₂ b).1 hball with heq | hadj
      · subst b
        exact False.elim (hbnot hc₂mem)
      · exact hadj
    have hc₃b : H.Adj c₃ b := by
      have hball : b ∈ closedBall H 1 c₃ := hc₃eq.symm ▸ hbballa
      rcases (ball_one_iff_induced c₃ b).1 hball with heq | hadj
      · subst b
        exact False.elim (hbnot hc₃mem)
      · exact hadj
    have hc₁c₂adj : H.Adj c₁ c₂ := by
      have hself : c₂ ∈ closedBall H 1 c₂ :=
        (ball_one_iff_induced c₂ c₂).2 (Or.inl rfl)
      have hball : c₂ ∈ closedBall H 1 c₁ := by
        rw [hc₁eq, ← hc₂eq]
        exact hself
      rcases (ball_one_iff_induced c₁ c₂).1 hball with heq | hadj
      · exact False.elim (hc₁c₂ heq.symm)
      · exact hadj
    have hc₁c₃adj : H.Adj c₁ c₃ := by
      have hself : c₃ ∈ closedBall H 1 c₃ :=
        (ball_one_iff_induced c₃ c₃).2 (Or.inl rfl)
      have hball : c₃ ∈ closedBall H 1 c₁ := by
        rw [hc₁eq, ← hc₃eq]
        exact hself
      rcases (ball_one_iff_induced c₁ c₃).1 hball with heq | hadj
      · exact False.elim (hc₁c₃ heq.symm)
      · exact hadj
    have hc₂c₃adj : H.Adj c₂ c₃ := by
      have hself : c₃ ∈ closedBall H 1 c₃ :=
        (ball_one_iff_induced c₃ c₃).2 (Or.inl rfl)
      have hball : c₃ ∈ closedBall H 1 c₂ := by
        rw [hc₂eq, ← hc₃eq]
        exact hself
      rcases (ball_one_iff_induced c₂ c₃).1 hball with heq | hadj
      · exact False.elim (hc₂c₃ heq.symm)
      · exact hadj
    have hbc₁_ne := hc₁b.ne.symm
    have hbc₂_ne := hc₂b.ne.symm
    have hbc₃_ne := hc₃b.ne.symm
    let f : Fin 4 → W := ![b, c₁, c₂, c₃]
    apply false_of_k4_configuration houterH f
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [f, hbc₁_ne, hbc₂_ne, hbc₃_ne,
          hc₁b.ne, hc₂b.ne, hc₃b.ne,
          hc₁c₂, hc₁c₃, hc₂c₃,
          hc₁c₂.symm, hc₁c₃.symm, hc₂c₃.symm] at hij ⊢
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [f, hc₁b, hc₂b, hc₃b, hc₁b.symm, hc₂b.symm, hc₃b.symm,
          hc₁c₂adj, hc₁c₃adj, hc₂c₃adj,
          hc₁c₂adj.symm, hc₁c₃adj.symm, hc₂c₃adj.symm] at hij ⊢

  let repairWitness (a b : W) : V :=
    if h :
        ¬ closedBall G 1 (a : V) ⊆ closedBall G 1 (b : V) then
      Classical.choose (Set.not_subset.mp h)
    else
      (a : V)
  have repairWitness_spec (a b : W)
      (h : ¬ closedBall G 1 (a : V) ⊆
        closedBall G 1 (b : V)) :
      repairWitness a b ∈ closedBall G 1 (a : V) ∧
      repairWitness a b ∉ closedBall G 1 (b : V) := by
    simp only [repairWitness, dif_pos h]
    exact Classical.choose_spec (Set.not_subset.mp h)

  let repairCandidates (a : W) : Finset W :=
    (twins a).erase a |>.filter fun b =>
      ¬ closedBall G 1 (a : V) ⊆ closedBall G 1 (b : V)
  let repairLabels (a : W) : Finset V :=
    (repairCandidates a).image fun b => repairWitness a b
  let baseLabels (a : W) : Finset V :=
    (A a).map ⟨Subtype.val, Subtype.val_injective⟩
  let layerLabels (a : W) : Finset V :=
    if (twins a).card = 3 then
      insert (a : V) (repairLabels a)
    else
      baseLabels a ∪ repairLabels a

  have repair_mem (a b : W)
      (htwin : b ∈ twins a) (hne : b ≠ a)
      (hdiff : ¬ closedBall G 1 (a : V) ⊆
        closedBall G 1 (b : V)) :
      repairWitness a b ∈ repairLabels a := by
    apply Finset.mem_image.mpr
    refine ⟨b, ?_, rfl⟩
    simp [repairCandidates, htwin, hne, hdiff]

  have repair_mem_layer (a b : W)
      (htwin : b ∈ twins a) (hne : b ≠ a)
      (hdiff : ¬ closedBall G 1 (a : V) ⊆
        closedBall G 1 (b : V)) :
      repairWitness a b ∈ layerLabels a := by
    have hmem := repair_mem a b htwin hne hdiff
    simp only [layerLabels]
    split
    · exact Finset.mem_insert_of_mem hmem
    · exact Finset.mem_union_right _ hmem

  have base_mem_layer (a : W)
      (hcard : (twins a).card ≠ 3) {x : V}
      (hx : x ∈ baseLabels a) :
      x ∈ layerLabels a := by
    simp [layerLabels, hcard, hx]

  have repairCandidates_card_le_erase (a : W) :
      (repairCandidates a).card ≤ ((twins a).erase a).card := by
    exact Finset.card_filter_le _ _
  have erase_twins_card (a : W) :
      ((twins a).erase a).card + 1 = (twins a).card := by
    simpa using Finset.card_erase_add_one (self_mem_twins a)
  have repairLabels_card_le (a : W) :
      (repairLabels a).card ≤ (repairCandidates a).card := by
    exact Finset.card_image_le

  have repair_card_le_two (a : W)
      (hcard : (twins a).card = 3) :
      (repairLabels a).card ≤ 2 := by
    have h₁ := repairLabels_card_le a
    have h₂ := repairCandidates_card_le_erase a
    have h₃ := erase_twins_card a
    omega

  have repair_card_le_one (a : W)
      (hcard : (twins a).card ≠ 3) :
      (repairLabels a).card ≤ 1 := by
    have htwins := twins_card_le_three a
    have htwins_two : (twins a).card ≤ 2 := by omega
    have h₁ := repairLabels_card_le a
    have h₂ := repairCandidates_card_le_erase a
    have h₃ := erase_twins_card a
    omega

  have base_card_le_two (a : W) : (baseLabels a).card ≤ 2 := by
    simpa [baseLabels] using hAwidth a

  have layer_card_le_three (a : W) :
      (layerLabels a).card ≤ 3 := by
    by_cases hcard : (twins a).card = 3
    · have hrepair := repair_card_le_two a hcard
      have hinsert :=
        Finset.card_insert_le (a : V) (repairLabels a)
      simp only [layerLabels, if_pos hcard]
      omega
    · have hrepair := repair_card_le_one a hcard
      have hbase := base_card_le_two a
      have hunion :=
        Finset.card_union_le (baseLabels a) (repairLabels a)
      simp only [layerLabels, if_neg hcard]
      omega

  have base_positive (a : W) {x : V}
      (hx : x ∈ baseLabels a) :
      x ∈ closedBall G 1 (a : V) := by
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
    have hyball : y ∈ closedBall H 1 a := hApositive hy
    have hambient :
        (y : V) ∈ closedBall G 1 (a : V) :=
      (ball_transport a y).1 hyball
    subst x
    exact hambient

  have repair_positive (a : W) {x : V}
      (hx : x ∈ repairLabels a) :
      x ∈ closedBall G 1 (a : V) := by
    obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp hx
    have hbfilter :
        ¬ closedBall G 1 (a : V) ⊆
          closedBall G 1 (b : V) := by
      exact (Finset.mem_filter.mp hb).2
    have hspec := (repairWitness_spec a b hbfilter).1
    simpa [hbx] using hspec

  have layer_positive (a : W) {x : V}
      (hx : x ∈ layerLabels a) :
      x ∈ closedBall G 1 (a : V) := by
    by_cases hcard : (twins a).card = 3
    · simp only [layerLabels, if_pos hcard, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact
          (ball_one_iff_ambient (a : V) (a : V)).2 (Or.inl rfl)
      · exact repair_positive a hx
    · simp only [layerLabels, if_neg hcard, Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact base_positive a hx
      · exact repair_positive a hx

  let S : TeachingMap V 1 := fun w =>
    if hw : w ∈ U then
      layerLabels ⟨w, by simpa [W] using hw⟩
    else
      ∅

  have S_at (w : V) (hw : w ∈ U) :
      S w = layerLabels ⟨w, by simpa [W] using hw⟩ := by
    simp [S, hw]

  have local_witness_to_ambient {a b x : W}
      (h : IsWitness H 1 x a b) :
      IsWitness G 1 (x : V) (a : V) (b : V) := by
    exact ⟨(ball_transport a x).1 h.1,
      fun hxb => h.2 ((ball_transport b x).2 hxb)⟩

  have layer_separates (a b : W)
      (hdifferent :
        DistinctConcepts G 1 (a : V) (b : V)) :
      ∃ x : V,
        (x ∈ layerLabels a ∨ x ∈ layerLabels b) ∧
        (IsWitness G 1 x (a : V) (b : V) ∨
          IsWitness G 1 x (b : V) (a : V)) := by
    by_cases htwin :
        closedBall H 1 a = closedBall H 1 b
    · have hbTwin : b ∈ twins a := by
        simp [twins, htwin.symm]
      have haTwin : a ∈ twins b := twin_symm hbTwin
      by_cases hsubset :
          closedBall G 1 (a : V) ⊆ closedBall G 1 (b : V)
      · have hnreverse :
            ¬ closedBall G 1 (b : V) ⊆
              closedBall G 1 (a : V) := by
          intro hreverse
          exact hdifferent
            (Set.Subset.antisymm hsubset hreverse)
        have hab : a ≠ b := by
          intro h
          subst b
          exact hdifferent rfl
        let x := repairWitness b a
        have hxmem :
            x ∈ layerLabels b :=
          repair_mem_layer b a haTwin hab hnreverse
        have hxspec := repairWitness_spec b a hnreverse
        exact ⟨x, Or.inr hxmem, Or.inr hxspec⟩
      · have hab : b ≠ a := by
          intro h
          subst b
          exact hdifferent rfl
        let x := repairWitness a b
        have hxmem :
            x ∈ layerLabels a :=
          repair_mem_layer a b hbTwin hab hsubset
        have hxspec := repairWitness_spec a b hsubset
        exact ⟨x, Or.inl hxmem, Or.inl hxspec⟩
    · have hbnot : b ∉ twins a := by
        intro h
        have heq : closedBall H 1 b = closedBall H 1 a := by
          simpa [twins] using h
        exact htwin heq.symm
      have hanot : a ∉ twins b := by
        intro h
        have heq : closedBall H 1 a = closedBall H 1 b := by
          simpa [twins] using h
        exact htwin heq
      by_cases hcarda : (twins a).card = 3
      · have hnab := twins_three_isolated a b hcarda hbnot
        have hab : (a : V) ≠ (b : V) := by
          intro h
          exact htwin (congrArg (closedBall H 1) (Subtype.ext h))
        have hanball :
            (a : V) ∉ closedBall G 1 (b : V) := by
          intro hball
          rcases (ball_one_iff_ambient (b : V) (a : V)).1 hball with
              heq | hadj
          · exact hab heq
          · exact hnab hadj.symm
        have haself :
            (a : V) ∈ layerLabels a := by
          simp [layerLabels, hcarda]
        exact ⟨a, Or.inl haself,
          Or.inl ⟨
            (ball_one_iff_ambient (a : V) (a : V)).2 (Or.inl rfl),
            hanball⟩⟩
      · by_cases hcardb : (twins b).card = 3
        · have hnba := twins_three_isolated b a hcardb hanot
          have hba : (b : V) ≠ (a : V) := by
            intro h
            exact htwin (congrArg (closedBall H 1) (Subtype.ext h.symm))
          have hbnotball :
              (b : V) ∉ closedBall G 1 (a : V) := by
            intro hball
            rcases (ball_one_iff_ambient (a : V) (b : V)).1 hball with
                heq | hadj
            · exact hba heq
            · exact hnba hadj.symm
          have hbself :
              (b : V) ∈ layerLabels b := by
            simp [layerLabels, hcardb]
          exact ⟨b, Or.inr hbself,
            Or.inr ⟨
              (ball_one_iff_ambient (b : V) (b : V)).2 (Or.inl rfl),
              hbnotball⟩⟩
        · obtain ⟨x, hxsets, hxwitness⟩ :=
            hAnoclash htwin
          refine ⟨(x : V), ?_, ?_⟩
          · rcases hxsets with hx | hx
            · left
              apply base_mem_layer a hcarda
              exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
            · right
              apply base_mem_layer b hcardb
              exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
          · rcases hxwitness with hx | hx
            · exact Or.inl (local_witness_to_ambient hx)
            · exact Or.inr (local_witness_to_ambient hx)

  have hlayer : IsLayerAssignment G U S := by
    constructor
    · intro w hw
      let a : W := ⟨w, by simpa [W] using hw⟩
      constructor
      · rw [S_at w hw]
        exact layer_card_le_three a
      · intro x hx
        rw [S_at w hw] at hx
        exact layer_positive a hx
    · intro w₁ w₂ hw₁ hw₂ hdifferent
      let a : W := ⟨w₁, by simpa [W] using hw₁⟩
      let b : W := ⟨w₂, by simpa [W] using hw₂⟩
      obtain ⟨x, hxsets, hxwitness⟩ :=
        layer_separates a b hdifferent
      refine ⟨x, ?_, hxwitness⟩
      rcases hxsets with hx | hx
      · left
        simpa [a, S_at w₁ hw₁] using hx
      · right
        simpa [b, S_at w₂ hw₂] using hx

  refine ⟨S, hlayer, ?_, ?_⟩
  · intro w hw
    constructor
    · have hcard := hlayer.1 w hw |>.1
      have hinsert := Finset.card_insert_le v₀ (S w)
      simpa [anchoredTeaching] using hinsert.trans (by omega)
    · intro y hy
      simp only [anchoredTeaching, Finset.mem_insert] at hy
      rcases hy with hyv₀ | hy
      · subst y
        exact
          (ball_one_iff_ambient w v₀).2
            (Or.inr (hneighbors w hw).symm)
      · exact (hlayer.1 w hw).2 y hy
  · intro w hw x hx
    have hv₀x : v₀ ∉ closedBall G 1 x := by
      intro h
      rcases (ball_one_iff_ambient x v₀).1 h with heq | hadj
      · subst x
        exact hx
          ((ball_one_iff_ambient v₀ v₀).2 (Or.inl rfl))
      · exact hx
          ((ball_one_iff_ambient v₀ x).2 (Or.inr hadj.symm))
    exact ⟨v₀, by simp [anchoredTeaching], hv₀x⟩

end Lax60Proofs.OuterplanarLayer
