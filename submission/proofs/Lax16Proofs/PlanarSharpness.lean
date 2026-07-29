import Mathlib.Tactic
import Lax16.PlanarSharpness

namespace Lax16Proofs.PlanarSharpness

open Lax16.PlanarGraphs
open Lax16.TeachingMaps
open Lax16.PlanarSharpness

/-- Membership in a radius-one ball is equality with the center or adjacency. -/
lemma mem_closedBall_one_iff {V : Type*} {G : SimpleGraph V} {v w : V} :
    w ∈ closedBall G 1 v ↔ w = v ∨ G.Adj v w := by
  constructor
  · rintro ⟨p, hp⟩
    by_cases hzero : p.length = 0
    · left
      exact (p.eq_of_length_eq_zero hzero).symm
    · right
      apply p.adj_of_length_eq_one
      omega
  · rintro (rfl | hadj)
    · exact ⟨SimpleGraph.Walk.nil, by simp⟩
    · exact ⟨hadj.toWalk, by simp⟩

/-- The label omitted by the explicit width-four teaching set. -/
def wheelOmitted (v : Fin 5) : Fin 5 :=
  if v = 0 then 0
  else if v = 1 then 3
  else if v = 2 then 4
  else if v = 3 then 1
  else 2

/-- The five closed balls of the wheel, represented as explicit finsets. -/
def wheelBall (v : Fin 5) : Finset (Fin 5) :=
  if v = 0 then Finset.univ else Finset.univ.erase (wheelOmitted v)

/-- A width-four teaching map: every vertex omits one label. -/
def wheelTeaching : TeachingMap (Fin 5) 1 :=
  fun v => Finset.univ.erase (wheelOmitted v)

lemma wheel_closedBall_iff (v x : Fin 5) :
    x ∈ closedBall sharpPlanarGraph 1 v ↔ x ∈ wheelBall v := by
  classical
  rw [mem_closedBall_one_iff]
  fin_cases v <;> fin_cases x <;>
    simp [sharpPlanarGraph, SimpleGraph.edge_adj, wheelBall, wheelOmitted]

lemma wheel_closedBall_eq (v : Fin 5) :
    closedBall sharpPlanarGraph 1 v = (wheelBall v : Set (Fin 5)) := by
  ext x
  exact wheel_closedBall_iff v x

lemma sharpPlanarGraph_isPlanar : IsPlanar sharpPlanarGraph := by
  constructor
  · rintro ⟨model⟩
    have hsurjective : Function.Surjective model.branch :=
      ((Fintype.bijective_iff_injective_and_card
        (fun x : Fin 5 => model.branch x)).2
          ⟨model.branch.injective, rfl⟩).2
    have hadj_of_ne (x y : Fin 5) (hxy : x ≠ y) :
        sharpPlanarGraph.Adj x y := by
      obtain ⟨a, ha⟩ := hsurjective x
      obtain ⟨b, hb⟩ := hsurjective y
      have hab_ne : a ≠ b := by
        intro hab
        apply hxy
        rw [← ha, ← hb, hab]
      have hab : (⊤ : SimpleGraph (Fin 5)).Adj a b := by
        simpa using hab_ne
      let p := model.route hab
      have hp : p.IsPath := model.route_isPath hab
      have hpositive : 0 < p.length := by
        apply Nat.pos_of_ne_zero
        intro hzero
        apply hab_ne
        apply model.branch.injective
        exact p.eq_of_length_eq_zero hzero
      have hle : p.length ≤ 1 := by
        by_contra hnot
        have htwo : 2 ≤ p.length := by omega
        obtain ⟨c, hc⟩ := hsurjective (p.getVert 1)
        apply model.branch_avoids_interiors hab c
        rw [hc]
        refine ⟨p.getVert_mem_support 1, ?_, ?_⟩
        · intro hequal
          have hone :
              (1 : ℕ) = 0 :=
            (hp.getVert_eq_start_iff (i := 1) (by omega)).mp hequal
          omega
        · intro hequal
          have hone :
              (1 : ℕ) = p.length :=
            (hp.getVert_eq_end_iff (i := 1) (by omega)).mp hequal
          omega
      have hlength : p.length = 1 := by omega
      simpa [p, ha, hb] using p.adj_of_length_eq_one hlength
    have hmissing : ¬sharpPlanarGraph.Adj (1 : Fin 5) 3 := by
      simp [sharpPlanarGraph, SimpleGraph.edge_adj]
    exact hmissing (hadj_of_ne 1 3 (by decide))
  · rintro ⟨model⟩
    have hcard :=
      Fintype.card_le_of_injective model.branch model.branch.injective
    norm_num at hcard

lemma wheelTeaching_positive :
    IsPositive sharpPlanarGraph 1 wheelTeaching := by
  intro v x hx
  rw [wheel_closedBall_iff]
  by_cases hv : v = 0
  · simp [wheelBall, hv]
  · simpa [wheelTeaching, wheelBall, hv] using hx

lemma wheelTeaching_width :
    HasWidthAtMost wheelTeaching 4 := by
  intro v
  simp [wheelTeaching]

lemma wheelTeaching_noclash :
    IsNoClash sharpPlanarGraph 1 wheelTeaching := by
  intro v w hdifferent
  unfold DistinctConcepts at hdifferent
  rw [wheel_closedBall_eq v, wheel_closedBall_eq w] at hdifferent
  unfold Separates IsWitness
  simp only [wheel_closedBall_iff]
  have hfinite :
      ∀ a b : Fin 5, wheelBall a ≠ wheelBall b →
        ∃ x,
          (x ∈ wheelTeaching a ∨ x ∈ wheelTeaching b) ∧
          ((x ∈ wheelBall a ∧ x ∉ wheelBall b) ∨
            (x ∈ wheelBall b ∧ x ∉ wheelBall a)) := by
    decide
  have hdifferentFinset : wheelBall v ≠ wheelBall w := by
    intro hequal
    exact hdifferent (congrArg (fun s : Finset (Fin 5) => (s : Set (Fin 5))) hequal)
  exact hfinite v w hdifferentFinset

lemma center_needs_rim_labels {d : ℕ} {T : TeachingMap (Fin 5) 1}
    (hpositive : IsPositive sharpPlanarGraph 1 T)
    (hnoclash : IsNoClash sharpPlanarGraph 1 T)
    (hwidth : HasWidthAtMost T d) :
    4 ≤ d := by
  have hlabel (rim missing : Fin 5)
      (hballs :
        wheelBall 0 = Finset.univ ∧
        wheelBall rim = Finset.univ.erase missing) :
      missing ∈ T 0 := by
    have hdifferent : DistinctConcepts sharpPlanarGraph 1 0 rim := by
      unfold DistinctConcepts
      rw [wheel_closedBall_eq 0, wheel_closedBall_eq rim, hballs.1, hballs.2]
      intro hequal
      have hmemSet :
          missing ∈ (↑(Finset.univ : Finset (Fin 5)) : Set (Fin 5)) := by simp
      rw [hequal] at hmemSet
      exact ((Finset.mem_erase.mp hmemSet).1 rfl).elim
    rcases hnoclash hdifferent with ⟨x, hxteaching, hxwitness⟩
    have hxmissing : x = missing := by
      unfold IsWitness at hxwitness
      simp only [wheel_closedBall_iff] at hxwitness
      rw [hballs.1, hballs.2] at hxwitness
      simp only [Finset.mem_univ, Finset.mem_erase, true_and, not_and,
        not_true_eq_false, and_false, or_false] at hxwitness
      exact not_ne_iff.mp hxwitness
    subst x
    rcases hxteaching with hcenter | hrim
    · exact hcenter
    · have hball := hpositive hrim
      rw [wheel_closedBall_iff, hballs.2] at hball
      exact ((Finset.mem_erase.mp hball).1 rfl).elim
  have hone : (1 : Fin 5) ∈ T 0 := by
    apply hlabel 3 1
    constructor <;> decide
  have htwo : (2 : Fin 5) ∈ T 0 := by
    apply hlabel 4 2
    constructor <;> decide
  have hthree : (3 : Fin 5) ∈ T 0 := by
    apply hlabel 1 3
    constructor <;> decide
  have hfour : (4 : Fin 5) ∈ T 0 := by
    apply hlabel 2 4
    constructor <;> decide
  have hsubset :
      ({1, 2, 3, 4} : Finset (Fin 5)) ⊆ T 0 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hone
    · exact htwo
    · exact hthree
    · exact hfour
  have hfour_card : 4 ≤ (T 0).card := by
    have := Finset.card_le_card hsubset
    norm_num at this ⊢
    exact this
  exact hfour_card.trans (hwidth 0)

/--
---
conclusion: Lax16.PlanarSharpness.planar_bound_is_sharp
---
The five-vertex wheel is planar directly from the topological-model
definition.  An explicit map omitting one label at every vertex gives the
upper bound.  Conversely, distinguishing the universal center ball from the
four rim balls forces all four rim labels into the center's positive teaching
set.
-/
theorem planar_bound_is_sharp :
    IsPlanar sharpPlanarGraph ∧
    positiveNCTD sharpPlanarGraph 1 = 4 := by
  refine ⟨sharpPlanarGraph_isPlanar, ?_⟩
  apply le_antisymm
  · unfold positiveNCTD
    apply Nat.sInf_le
    exact ⟨wheelTeaching, wheelTeaching_positive,
      wheelTeaching_noclash, wheelTeaching_width⟩
  · unfold positiveNCTD
    apply le_csInf
    · exact ⟨4, wheelTeaching, wheelTeaching_positive,
        wheelTeaching_noclash, wheelTeaching_width⟩
    intro d hd
    rcases hd with ⟨T, hpositive, hnoclash, hwidth⟩
    exact center_needs_rim_labels hpositive hnoclash hwidth

end Lax16Proofs.PlanarSharpness
