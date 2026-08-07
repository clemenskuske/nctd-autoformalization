import Mathlib.Tactic
import Lax16.OuterplanarSharpness
import Lax16Proofs.PlanarSharpness

namespace Lax16Proofs.OuterplanarSharpness

open Lax16.OuterplanarSharpness
open Lax16.PlanarGraphs
open Lax16.TeachingMaps

/-- The six radius-one balls of the sharp outerplanar example. -/
def outerBall (v : Fin 6) : Finset (Fin 6) :=
  if v = 0 then {0, 1, 2, 3}
  else if v = 1 then {0, 1, 2, 4}
  else if v = 2 then {0, 1, 2}
  else if v = 3 then {0, 3, 4, 5}
  else if v = 4 then {1, 3, 4, 5}
  else {3, 4, 5}

/-- An explicit positive teaching map of width two. -/
def outerTeaching : TeachingMap (Fin 6) 1 :=
  fun v =>
    if v = 0 then {3}
    else if v = 1 then {4}
    else if v = 2 then ∅
    else if v = 3 then {0, 5}
    else if v = 4 then {1, 5}
    else {3, 4}

set_option maxHeartbeats 800000 in
lemma outer_closedBall_iff (v x : Fin 6) :
    x ∈ closedBall sharpOuterplanarGraph 1 v ↔ x ∈ outerBall v := by
  rw [Lax16Proofs.PlanarSharpness.mem_closedBall_one_iff]
  fin_cases v <;> fin_cases x <;>
    simp [sharpOuterplanarGraph, SimpleGraph.edge_adj, outerBall]

lemma outer_closedBall_eq (v : Fin 6) :
    closedBall sharpOuterplanarGraph 1 v = (outerBall v : Set (Fin 6)) := by
  ext x
  exact outer_closedBall_iff v x

/-- A computable presentation of adjacency in the explicit graph. -/
def outerAdj (v w : Fin 6) : Prop :=
  w ∈ outerBall v ∧ w ≠ v

instance (v w : Fin 6) : Decidable (outerAdj v w) := by
  unfold outerAdj
  infer_instance

lemma outer_adj_iff (v w : Fin 6) :
    sharpOuterplanarGraph.Adj v w ↔ outerAdj v w := by
  unfold outerAdj
  rw [← outer_closedBall_iff, Lax16Proofs.PlanarSharpness.mem_closedBall_one_iff]
  constructor
  · intro hadj
    exact ⟨Or.inr hadj, hadj.ne.symm⟩
  · rintro ⟨heq | hadj, hne⟩
    · exact (hne heq).elim
    · exact hadj

lemma outerTeaching_positive :
    IsPositive sharpOuterplanarGraph 1 outerTeaching := by
  intro v x hx
  rw [outer_closedBall_iff]
  fin_cases v <;> fin_cases x <;>
    simp [outerTeaching, outerBall] at hx ⊢

lemma outerTeaching_width :
    HasWidthAtMost outerTeaching 2 := by
  intro v
  fin_cases v <;> decide

lemma outerTeaching_noclash :
    IsNoClash sharpOuterplanarGraph 1 outerTeaching := by
  intro v w hdifferent
  unfold DistinctConcepts at hdifferent
  rw [outer_closedBall_eq v, outer_closedBall_eq w] at hdifferent
  unfold Separates IsWitness
  simp only [outer_closedBall_iff]
  have hfinite :
      ∀ a b : Fin 6, outerBall a ≠ outerBall b →
        ∃ x,
          (x ∈ outerTeaching a ∨ x ∈ outerTeaching b) ∧
          ((x ∈ outerBall a ∧ x ∉ outerBall b) ∨
            (x ∈ outerBall b ∧ x ∉ outerBall a)) := by
    decide
  apply hfinite v w
  intro hequal
  exact hdifferent
    (congrArg (fun s : Finset (Fin 6) => (s : Set (Fin 6))) hequal)

lemma no_width_one_noclash {T : TeachingMap (Fin 6) 1}
    (hnoclash : IsNoClash sharpOuterplanarGraph 1 T)
    (hwidth : HasWidthAtMost T 1) : False := by
  have separation (a b : Fin 6) (hdifferent : outerBall a ≠ outerBall b) :
      ∃ x,
        (x ∈ T a ∨ x ∈ T b) ∧
        ((x ∈ outerBall a ∧ x ∉ outerBall b) ∨
          (x ∈ outerBall b ∧ x ∉ outerBall a)) := by
    have hdifferent' : DistinctConcepts sharpOuterplanarGraph 1 a b := by
      unfold DistinctConcepts
      rw [outer_closedBall_eq a, outer_closedBall_eq b]
      intro hequal
      exact hdifferent
        (Finset.coe_injective hequal)
    rcases hnoclash hdifferent' with ⟨x, hxsets, hxwitness⟩
    unfold IsWitness at hxwitness
    exact ⟨x, hxsets, by
      simpa only [outer_closedBall_iff] using hxwitness⟩
  have forced (a b label : Fin 6)
      (hdifferent : outerBall a ≠ outerBall b)
      (hunique :
        ∀ x : Fin 6,
          ((x ∈ outerBall a ∧ x ∉ outerBall b) ∨
            (x ∈ outerBall b ∧ x ∉ outerBall a)) ↔ x = label) :
      label ∈ T a ∨ label ∈ T b := by
    rcases separation a b hdifferent with ⟨x, hxsets, hxwitness⟩
    have : x = label := (hunique x).mp hxwitness
    simpa [this] using hxsets
  have h02 : (3 : Fin 6) ∈ T 0 ∨ (3 : Fin 6) ∈ T 2 := by
    apply forced 0 2 3 <;> decide
  have h12 : (4 : Fin 6) ∈ T 1 ∨ (4 : Fin 6) ∈ T 2 := by
    apply forced 1 2 4 <;> decide
  have h35 : (0 : Fin 6) ∈ T 3 ∨ (0 : Fin 6) ∈ T 5 := by
    apply forced 3 5 0 <;> decide
  have h45 : (1 : Fin 6) ∈ T 4 ∨ (1 : Fin 6) ∈ T 5 := by
    apply forced 4 5 1 <;> decide
  have hleft : (3 : Fin 6) ∈ T 0 ∨ (4 : Fin 6) ∈ T 1 := by
    rcases h02 with h03 | h23
    · exact Or.inl h03
    · rcases h12 with h14 | h24
      · exact Or.inr h14
      · have hequal :=
          (Finset.card_le_one.mp (hwidth 2)) 3 h23 4 h24
        exact (by omega)
  have hright : (0 : Fin 6) ∈ T 3 ∨ (1 : Fin 6) ∈ T 4 := by
    rcases h35 with h30 | h50
    · exact Or.inl h30
    · rcases h45 with h41 | h51
      · exact Or.inr h41
      · have hequal :=
          (Finset.card_le_one.mp (hwidth 5)) 0 h50 1 h51
        exact (by omega)
  have incompatible (a b la lb : Fin 6)
      (hla : la ∈ T a) (hlb : lb ∈ T b)
      (hdifferent : outerBall a ≠ outerBall b)
      (hla_not :
        ¬((la ∈ outerBall a ∧ la ∉ outerBall b) ∨
          (la ∈ outerBall b ∧ la ∉ outerBall a)))
      (hlb_not :
        ¬((lb ∈ outerBall a ∧ lb ∉ outerBall b) ∨
          (lb ∈ outerBall b ∧ lb ∉ outerBall a))) :
      False := by
    rcases separation a b hdifferent with ⟨x, hxsets, hxwitness⟩
    rcases hxsets with hxa | hxb
    · have hequal :=
        (Finset.card_le_one.mp (hwidth a)) x hxa la hla
      exact hla_not (hequal ▸ hxwitness)
    · have hequal :=
        (Finset.card_le_one.mp (hwidth b)) x hxb lb hlb
      exact hlb_not (hequal ▸ hxwitness)
  rcases hleft with h03 | h14 <;> rcases hright with h30 | h41
  · exact incompatible 0 3 3 0 h03 h30 (by decide) (by decide) (by decide)
  · exact incompatible 0 4 3 1 h03 h41 (by decide) (by decide) (by decide)
  · exact incompatible 1 3 4 0 h14 h30 (by decide) (by decide) (by decide)
  · exact incompatible 1 4 4 1 h14 h41 (by decide) (by decide) (by decide)

lemma nctd_sharp_values :
    nctd sharpOuterplanarGraph 1 = 2 ∧
    positiveNCTD sharpOuterplanarGraph 1 = 2 := by
  have hordinaryUpper : HasNCTDAtMost sharpOuterplanarGraph 1 2 :=
    ⟨outerTeaching, outerTeaching_noclash, outerTeaching_width⟩
  have hpositiveUpper : HasPositiveNCTDAtMost sharpOuterplanarGraph 1 2 :=
    ⟨outerTeaching, outerTeaching_positive,
      outerTeaching_noclash, outerTeaching_width⟩
  constructor
  · apply le_antisymm
    · unfold nctd
      exact Nat.sInf_le hordinaryUpper
    · unfold nctd
      apply le_csInf
      · exact ⟨2, hordinaryUpper⟩
      · intro d hd
        rcases hd with ⟨T, hnoclash, hwidth⟩
        by_contra hnot
        have hdle : d ≤ 1 := by omega
        exact no_width_one_noclash hnoclash
          (fun v => (hwidth v).trans hdle)
  · apply le_antisymm
    · unfold positiveNCTD
      exact Nat.sInf_le hpositiveUpper
    · unfold positiveNCTD
      apply le_csInf
      · exact ⟨2, hpositiveUpper⟩
      · intro d hd
        rcases hd with ⟨T, _, hnoclash, hwidth⟩
        by_contra hnot
        have hdle : d ≤ 1 := by omega
        exact no_width_one_noclash hnoclash
          (fun v => (hwidth v).trans hdle)

/--
A walk crossing out of a set contains a vertex in any set covering all
outgoing boundary endpoints.
-/
lemma walk_hits_boundary {V : Type*} {G : SimpleGraph V}
    (inside boundary : Set V)
    (hboundary :
      ∀ ⦃a b : V⦄, G.Adj a b → a ∈ inside → b ∉ inside → b ∈ boundary)
    {a b : V} (p : G.Walk a b) (ha : a ∈ inside) (hb : b ∉ inside) :
    ∃ x ∈ p.support, x ∈ boundary := by
  induction p with
  | nil => exact (hb ha).elim
  | @cons a c b hac p ih =>
      by_cases hc : c ∈ inside
      · rcases ih hc hb with ⟨x, hxsupport, hxboundary⟩
        exact ⟨x, by simp [hxsupport], hxboundary⟩
      · exact ⟨c, by simp, hboundary hac ha hc⟩

lemma walk_left_to_right_hits {a b : Fin 6}
    (p : sharpOuterplanarGraph.Walk a b)
    (ha : a ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hb : b ∈ ({3, 4, 5} : Finset (Fin 6))) :
    ∃ x ∈ p.support, x = 3 ∨ x = 4 := by
  let inside : Set (Fin 6) := ↑({0, 1, 2} : Finset (Fin 6))
  let boundary : Set (Fin 6) := {3, 4}
  have hedge :
      ∀ ⦃u v : Fin 6⦄, sharpOuterplanarGraph.Adj u v →
        u ∈ inside → v ∉ inside → v ∈ boundary := by
    intro u v huv hu hv
    rw [outer_adj_iff] at huv
    have hfinite :
        ∀ u v : Fin 6, outerAdj u v →
          u ∈ inside → v ∉ inside → v ∈ boundary := by
      decide
    exact hfinite u v huv hu hv
  have ha' : a ∈ inside := by simpa [inside] using ha
  have hb' : b ∉ inside := by
    fin_cases b <;> simp [inside] at hb ⊢
  rcases walk_hits_boundary inside boundary hedge p ha' hb' with
    ⟨x, hxsupport, hxboundary⟩
  exact ⟨x, hxsupport, by simpa [boundary, Set.mem_insert_iff] using hxboundary⟩

lemma walk_right_to_left_hits {a b : Fin 6}
    (p : sharpOuterplanarGraph.Walk a b)
    (ha : a ∈ ({3, 4, 5} : Finset (Fin 6)))
    (hb : b ∈ ({0, 1, 2} : Finset (Fin 6))) :
    ∃ x ∈ p.support, x = 0 ∨ x = 1 := by
  let inside : Set (Fin 6) := ↑({3, 4, 5} : Finset (Fin 6))
  let boundary : Set (Fin 6) := {0, 1}
  have hedge :
      ∀ ⦃u v : Fin 6⦄, sharpOuterplanarGraph.Adj u v →
        u ∈ inside → v ∉ inside → v ∈ boundary := by
    intro u v huv hu hv
    rw [outer_adj_iff] at huv
    have hfinite :
        ∀ u v : Fin 6, outerAdj u v →
          u ∈ inside → v ∉ inside → v ∈ boundary := by
      decide
    exact hfinite u v huv hu hv
  have ha' : a ∈ inside := by simpa [inside] using ha
  have hb' : b ∉ inside := by
    fin_cases b <;> simp [inside] at hb ⊢
  rcases walk_hits_boundary inside boundary hedge p ha' hb' with
    ⟨x, hxsupport, hxboundary⟩
  exact ⟨x, hxsupport, by simpa [boundary, Set.mem_insert_iff] using hxboundary⟩

lemma walk_zero_to_four_hits (p : sharpOuterplanarGraph.Walk 0 4) :
    ∃ x ∈ p.support, x = 1 ∨ x = 3 := by
  let inside : Set (Fin 6) := ↑({0, 2} : Finset (Fin 6))
  let boundary : Set (Fin 6) := {1, 3}
  have hedge :
      ∀ ⦃u v : Fin 6⦄, sharpOuterplanarGraph.Adj u v →
        u ∈ inside → v ∉ inside → v ∈ boundary := by
    intro u v huv hu hv
    rw [outer_adj_iff] at huv
    have hfinite :
        ∀ u v : Fin 6, outerAdj u v →
          u ∈ inside → v ∉ inside → v ∈ boundary := by
      decide
    exact hfinite u v huv hu hv
  rcases walk_hits_boundary inside boundary hedge p
      (by simp [inside]) (by simp [inside]) with
    ⟨x, hxsupport, hxboundary⟩
  exact ⟨x, hxsupport, by simpa [boundary, Set.mem_insert_iff] using hxboundary⟩

lemma walk_one_to_three_hits (p : sharpOuterplanarGraph.Walk 1 3) :
    ∃ x ∈ p.support, x = 0 ∨ x = 4 := by
  let inside : Set (Fin 6) := ↑({1, 2} : Finset (Fin 6))
  let boundary : Set (Fin 6) := {0, 4}
  have hedge :
      ∀ ⦃u v : Fin 6⦄, sharpOuterplanarGraph.Adj u v →
        u ∈ inside → v ∉ inside → v ∈ boundary := by
    intro u v huv hu hv
    rw [outer_adj_iff] at huv
    have hfinite :
        ∀ u v : Fin 6, outerAdj u v →
          u ∈ inside → v ∉ inside → v ∈ boundary := by
      decide
    exact hfinite u v huv hu hv
  rcases walk_hits_boundary inside boundary hedge p
      (by simp [inside]) (by simp [inside]) with
    ⟨x, hxsupport, hxboundary⟩
  exact ⟨x, hxsupport, by simpa [boundary, Set.mem_insert_iff] using hxboundary⟩

lemma route_not_nil {W : Type*} {H : SimpleGraph W}
    (model : TopologicalModel H sharpOuterplanarGraph)
    {a b : W} (hab : H.Adj a b) :
    ¬(model.route hab).Nil := by
  intro hnil
  apply hab.ne
  apply model.branch.injective
  exact (model.route hab).eq_of_length_eq_zero hnil.length_eq_zero

lemma route_snd_eq_end_or_interior {W : Type*} {H : SimpleGraph W}
    (model : TopologicalModel H sharpOuterplanarGraph)
    {a b : W} (hab : H.Adj a b) :
    (model.route hab).snd = model.branch b ∨
      (model.route hab).snd ∈ walkInterior (model.route hab) := by
  let p := model.route hab
  have hp : p.IsPath := model.route_isPath hab
  have hpositive : 0 < p.length := by
    simpa [SimpleGraph.Walk.not_nil_iff_lt_length] using route_not_nil model hab
  by_cases hone : p.length = 1
  · left
    simpa [p, hone] using p.getVert_length
  · right
    have htwo : 2 ≤ p.length := by omega
    refine ⟨p.getVert_mem_support 1, ?_, ?_⟩
    · intro hequal
      have : (1 : ℕ) = 0 :=
        (hp.getVert_eq_start_iff (i := 1) (by omega)).mp hequal
      omega
    · intro hequal
      have : (1 : ℕ) = p.length :=
        (hp.getVert_eq_end_iff (i := 1) (by omega)).mp hequal
      omega

lemma route_snd_ne {W : Type*} {H : SimpleGraph W}
    (model : TopologicalModel H sharpOuterplanarGraph)
    {a b c : W} (hab : H.Adj a b) (hac : H.Adj a c) (hbc : b ≠ c) :
    (model.route hab).snd ≠ (model.route hac).snd := by
  intro hequal
  rcases route_snd_eq_end_or_interior model hab with hendb | hinterb
  · rcases route_snd_eq_end_or_interior model hac with hendc | hinterc
    · apply hbc
      apply model.branch.injective
      exact hendb.symm.trans (hequal.trans hendc)
    · apply model.branch_avoids_interiors hac b
      rwa [← hendb, hequal]
  · rcases route_snd_eq_end_or_interior model hac with hendc | hinterc
    · apply model.branch_avoids_interiors hab c
      rwa [← hendc, ← hequal]
    · have hedges :
          ¬((a = a ∧ b = c) ∨ (a = c ∧ b = a)) := by
        rintro (⟨_, h⟩ | ⟨h, _⟩)
        · exact hbc h
        · exact hac.ne h
      have hdisjoint :=
        model.route_interiors_disjoint hab hac hedges
      exact Set.disjoint_left.mp hdisjoint hinterb
        (hequal ▸ hinterc)

lemma three_route_neighbors {W : Type*} {H : SimpleGraph W}
    (model : TopologicalModel H sharpOuterplanarGraph)
    {a b c d : W}
    (hab : H.Adj a b) (hac : H.Adj a c) (had : H.Adj a d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ x y z : Fin 6,
      sharpOuterplanarGraph.Adj (model.branch a) x ∧
      sharpOuterplanarGraph.Adj (model.branch a) y ∧
      sharpOuterplanarGraph.Adj (model.branch a) z ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  let x := (model.route hab).snd
  let y := (model.route hac).snd
  let z := (model.route had).snd
  refine ⟨x, y, z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact SimpleGraph.Walk.adj_snd (route_not_nil model hab)
  · exact SimpleGraph.Walk.adj_snd (route_not_nil model hac)
  · exact SimpleGraph.Walk.adj_snd (route_not_nil model had)
  · exact route_snd_ne model hab hac hbc
  · exact route_snd_ne model hab had hbd
  · exact route_snd_ne model hac had hcd

lemma branch_not_mem_route_support {W : Type*} {H : SimpleGraph W}
    (model : TopologicalModel H sharpOuterplanarGraph)
    {a b c : W} (hab : H.Adj a b) (hca : c ≠ a) (hcb : c ≠ b) :
    model.branch c ∉ (model.route hab).support := by
  intro hsupport
  apply model.branch_avoids_interiors hab c
  exact ⟨hsupport,
    fun h => hca (model.branch.injective h),
    fun h => hcb (model.branch.injective h)⟩

/-- The four vertices of degree three in the explicit graph. -/
def IsHighVertex (v : Fin 6) : Prop :=
  v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 4

instance (v : Fin 6) : Decidable (IsHighVertex v) := by
  unfold IsHighVertex
  infer_instance

lemma high_of_three_neighbors {u x y z : Fin 6}
    (hux : sharpOuterplanarGraph.Adj u x)
    (huy : sharpOuterplanarGraph.Adj u y)
    (huz : sharpOuterplanarGraph.Adj u z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    IsHighVertex u := by
  rw [outer_adj_iff] at hux huy huz
  have hfinite :
      ∀ u x y z : Fin 6,
        outerAdj u x → outerAdj u y → outerAdj u z →
        x ≠ y → x ≠ z → y ≠ z → IsHighVertex u := by
    decide
  exact hfinite u x y z hux huy huz hxy hxz hyz

lemma route_snd_ne_other_branch {W : Type*} {H : SimpleGraph W}
    (model : TopologicalModel H sharpOuterplanarGraph)
    {a b c : W} (hab : H.Adj a b) (hcb : c ≠ b) :
    (model.route hab).snd ≠ model.branch c := by
  intro hequal
  rcases route_snd_eq_end_or_interior model hab with hend | hinterior
  · apply hcb
    apply model.branch.injective
    exact hequal.symm.trans hend
  · apply model.branch_avoids_interiors hab c
    rwa [← hequal]

lemma no_topological_K4 :
    ¬HasTopologicalModel (⊤ : SimpleGraph (Fin 4))
      sharpOuterplanarGraph := by
  rintro ⟨model⟩
  have hhigh (a : Fin 4) : IsHighVertex (model.branch a) := by
    fin_cases a
    · rcases three_route_neighbors model
          (a := (0 : Fin 4)) (b := 1) (c := 2) (d := 3)
          (by simp) (by simp) (by simp) (by decide) (by decide) (by decide) with
        ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩
      exact high_of_three_neighbors hx hy hz hxy hxz hyz
    · rcases three_route_neighbors model
          (a := (1 : Fin 4)) (b := 0) (c := 2) (d := 3)
          (by simp) (by simp) (by simp) (by decide) (by decide) (by decide) with
        ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩
      exact high_of_three_neighbors hx hy hz hxy hxz hyz
    · rcases three_route_neighbors model
          (a := (2 : Fin 4)) (b := 0) (c := 1) (d := 3)
          (by simp) (by simp) (by simp) (by decide) (by decide) (by decide) with
        ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩
      exact high_of_three_neighbors hx hy hz hxy hxz hyz
    · rcases three_route_neighbors model
          (a := (3 : Fin 4)) (b := 0) (c := 1) (d := 2)
          (by simp) (by simp) (by simp) (by decide) (by decide) (by decide) with
        ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩
      exact high_of_three_neighbors hx hy hz hxy hxz hyz
  let highVertices : Finset (Fin 6) := {0, 1, 3, 4}
  let branchHigh : Fin 4 ↪ {v : Fin 6 // v ∈ highVertices} :=
    { toFun := fun a => ⟨model.branch a, by
        simpa [highVertices, IsHighVertex] using hhigh a⟩
      inj' := fun _ _ h => model.branch.injective (congrArg Subtype.val h) }
  have hsurjective : Function.Surjective branchHigh := by
    exact ((Fintype.bijective_iff_injective_and_card branchHigh).2
      ⟨branchHigh.injective, by decide⟩).2
  obtain ⟨a0, ha0⟩ :=
    hsurjective (⟨0, by simp [highVertices]⟩ :
      {v : Fin 6 // v ∈ highVertices})
  obtain ⟨a1, ha1⟩ :=
    hsurjective (⟨1, by simp [highVertices]⟩ :
      {v : Fin 6 // v ∈ highVertices})
  obtain ⟨a3, ha3⟩ :=
    hsurjective (⟨3, by simp [highVertices]⟩ :
      {v : Fin 6 // v ∈ highVertices})
  obtain ⟨a4, ha4⟩ :=
    hsurjective (⟨4, by simp [highVertices]⟩ :
      {v : Fin 6 // v ∈ highVertices})
  have ha0' : model.branch a0 = 0 := congrArg Subtype.val ha0
  have ha1' : model.branch a1 = 1 := congrArg Subtype.val ha1
  have ha3' : model.branch a3 = 3 := congrArg Subtype.val ha3
  have ha4' : model.branch a4 = 4 := congrArg Subtype.val ha4
  have ha04 : a0 ≠ a4 := by
    intro h
    subst a4
    rw [ha0'] at ha4'
    omega
  have hroute : (⊤ : SimpleGraph (Fin 4)).Adj a0 a4 := by
    simpa using ha04
  let p04 : sharpOuterplanarGraph.Walk 0 4 :=
    (model.route hroute).copy ha0' ha4'
  rcases walk_zero_to_four_hits p04 with
    ⟨x, hxsupport, hx⟩
  have hxsupport' : x ∈ (model.route hroute).support := by
    simpa [p04] using hxsupport
  rcases hx with rfl | rfl
  · apply branch_not_mem_route_support model hroute
      (c := a1) (by
        intro h
        subst a1
        rw [ha0'] at ha1'
        omega) (by
        intro h
        subst a1
        rw [ha4'] at ha1'
        omega)
    rw [ha1']
    exact hxsupport'
  · apply branch_not_mem_route_support model hroute
      (c := a3) (by
        intro h
        subst a3
        rw [ha0'] at ha3'
        omega) (by
        intro h
        subst a3
        rw [ha4'] at ha3'
        omega)
    rw [ha3']
    exact hxsupport'

set_option maxHeartbeats 2000000 in
lemma no_topological_K23 :
    ¬HasTopologicalModel
      (completeBipartiteGraph (Fin 2) (Fin 3))
      sharpOuterplanarGraph := by
  rintro ⟨model⟩
  let left0 : Sum (Fin 2) (Fin 3) := Sum.inl 0
  let left1 : Sum (Fin 2) (Fin 3) := Sum.inl 1
  let right0 : Sum (Fin 2) (Fin 3) := Sum.inr 0
  let right1 : Sum (Fin 2) (Fin 3) := Sum.inr 1
  let right2 : Sum (Fin 2) (Fin 3) := Sum.inr 2
  have h0r0 :
      (completeBipartiteGraph (Fin 2) (Fin 3)).Adj left0 right0 := by
    simp [left0, right0]
  have h0r1 :
      (completeBipartiteGraph (Fin 2) (Fin 3)).Adj left0 right1 := by
    simp [left0, right1]
  have h0r2 :
      (completeBipartiteGraph (Fin 2) (Fin 3)).Adj left0 right2 := by
    simp [left0, right2]
  have h1r0 :
      (completeBipartiteGraph (Fin 2) (Fin 3)).Adj left1 right0 := by
    simp [left1, right0]
  have h1r1 :
      (completeBipartiteGraph (Fin 2) (Fin 3)).Adj left1 right1 := by
    simp [left1, right1]
  have h1r2 :
      (completeBipartiteGraph (Fin 2) (Fin 3)).Adj left1 right2 := by
    simp [left1, right2]
  rcases three_route_neighbors model h0r0 h0r1 h0r2
      (by simp [right0, right1]) (by simp [right0, right2])
      (by simp [right1, right2]) with
    ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩
  have hhigh0 : IsHighVertex (model.branch left0) :=
    high_of_three_neighbors hx hy hz hxy hxz hyz
  let sx := (model.route h0r0).snd
  let sy := (model.route h0r1).snd
  let sz := (model.route h0r2).snd
  have hsx : sharpOuterplanarGraph.Adj (model.branch left0) sx :=
    SimpleGraph.Walk.adj_snd (route_not_nil model h0r0)
  have hsy : sharpOuterplanarGraph.Adj (model.branch left0) sy :=
    SimpleGraph.Walk.adj_snd (route_not_nil model h0r1)
  have hsz : sharpOuterplanarGraph.Adj (model.branch left0) sz :=
    SimpleGraph.Walk.adj_snd (route_not_nil model h0r2)
  have hsxy : sx ≠ sy :=
    route_snd_ne model h0r0 h0r1 (by simp [right0, right1])
  have hsxz : sx ≠ sz :=
    route_snd_ne model h0r0 h0r2 (by simp [right0, right2])
  have hsyz : sy ≠ sz :=
    route_snd_ne model h0r1 h0r2 (by simp [right1, right2])
  have hsxleft1 : sx ≠ model.branch left1 :=
    route_snd_ne_other_branch model h0r0 (by simp [right0])
  have hsyleft1 : sy ≠ model.branch left1 :=
    route_snd_ne_other_branch model h0r1 (by simp [right1])
  have hszleft1 : sz ≠ model.branch left1 :=
    route_snd_ne_other_branch model h0r2 (by simp [right2])
  have hnotadj :
      ¬sharpOuterplanarGraph.Adj
        (model.branch left0) (model.branch left1) := by
    intro hadj
    rw [outer_adj_iff] at hadj hsx hsy hsz
    have hfinite :
        ∀ u v x y z : Fin 6,
          outerAdj u v → outerAdj u x → outerAdj u y → outerAdj u z →
          x ≠ y → x ≠ z → y ≠ z →
          x ≠ v → y ≠ v → z ≠ v → False := by
      decide
    exact hfinite _ _ sx sy sz hadj hsx hsy hsz hsxy hsxz hsyz
      hsxleft1 hsyleft1 hszleft1
  rcases three_route_neighbors model h1r0 h1r1 h1r2
      (by simp [right0, right1]) (by simp [right0, right2])
      (by simp [right1, right2]) with
    ⟨x', y', z', hx', hy', hz', hxy', hxz', hyz'⟩
  have hhigh1 : IsHighVertex (model.branch left1) :=
    high_of_three_neighbors hx' hy' hz' hxy' hxz' hyz'
  have hleftne : model.branch left0 ≠ model.branch left1 :=
    fun h => (by
      have := model.branch.injective h
      simp [left0, left1] at this)
  have hopposite :
      (model.branch left0 = 0 ∧ model.branch left1 = 4) ∨
      (model.branch left0 = 4 ∧ model.branch left1 = 0) ∨
      (model.branch left0 = 1 ∧ model.branch left1 = 3) ∨
      (model.branch left0 = 3 ∧ model.branch left1 = 1) := by
    have hnotadj' :
        ¬outerAdj (model.branch left0) (model.branch left1) := by
      rwa [← outer_adj_iff]
    have hfinite :
        ∀ u v : Fin 6,
          IsHighVertex u → IsHighVertex v → u ≠ v → ¬outerAdj u v →
          (u = 0 ∧ v = 4) ∨ (u = 4 ∧ v = 0) ∨
          (u = 1 ∧ v = 3) ∨ (u = 3 ∧ v = 1) := by
      decide
    exact hfinite _ _ hhigh0 hhigh1 hleftne hnotadj'
  have impossible04
      (a0 a4 : Sum (Fin 2) (Fin 3))
      (ha0 : model.branch a0 = 0) (ha4 : model.branch a4 = 4)
      (ha0right : ∀ q : Fin 3, a0 ≠ Sum.inr q)
      (ha4right : ∀ q : Fin 3, a4 ≠ Sum.inr q)
      (ha04 : a0 ≠ a4)
      (ha0adj :
        ∀ q : Fin 3,
          (completeBipartiteGraph (Fin 2) (Fin 3)).Adj a0 (Sum.inr q))
      (ha4adj :
        ∀ q : Fin 3,
          (completeBipartiteGraph (Fin 2) (Fin 3)).Adj a4 (Sum.inr q)) :
      False := by
    let r0 := model.branch (Sum.inr (0 : Fin 3))
    let r1 := model.branch (Sum.inr (1 : Fin 3))
    let r2 := model.branch (Sum.inr (2 : Fin 3))
    have hr01 : r0 ≠ r1 := by
      intro h
      have := model.branch.injective h
      simp [r0, r1] at this
    have hr02 : r0 ≠ r2 := by
      intro h
      have := model.branch.injective h
      simp [r0, r2] at this
    have hr12 : r1 ≠ r2 := by
      intro h
      have := model.branch.injective h
      simp [r1, r2] at this
    let rightHas (v : Fin 6) : Prop := r0 = v ∨ r1 = v ∨ r2 = v
    have rightPreimage {v : Fin 6} (hv : rightHas v) :
        ∃ q : Fin 3, model.branch (Sum.inr q) = v := by
      rcases hv with h | h | h
      · exact ⟨0, by simpa [r0] using h⟩
      · exact ⟨1, by simpa [r1] using h⟩
      · exact ⟨2, by simpa [r2] using h⟩
    have hr0ne0 : r0 ≠ 0 := by
      intro h
      apply ha0right 0
      apply model.branch.injective
      simpa [r0] using ha0.trans h.symm
    have hr1ne0 : r1 ≠ 0 := by
      intro h
      apply ha0right 1
      apply model.branch.injective
      simpa [r1] using ha0.trans h.symm
    have hr2ne0 : r2 ≠ 0 := by
      intro h
      apply ha0right 2
      apply model.branch.injective
      simpa [r2] using ha0.trans h.symm
    have hr0ne4 : r0 ≠ 4 := by
      intro h
      apply ha4right 0
      apply model.branch.injective
      simpa [r0] using ha4.trans h.symm
    have hr1ne4 : r1 ≠ 4 := by
      intro h
      apply ha4right 1
      apply model.branch.injective
      simpa [r1] using ha4.trans h.symm
    have hr2ne4 : r2 ≠ 4 := by
      intro h
      apply ha4right 2
      apply model.branch.injective
      simpa [r2] using ha4.trans h.symm
    have hnotBoth : ¬(rightHas 1 ∧ rightHas 2) := by
      rintro ⟨hone, htwo⟩
      obtain ⟨q1, hq1⟩ := rightPreimage hone
      obtain ⟨q2, hq2⟩ := rightPreimage htwo
      have hq12 : q1 ≠ q2 := by
        intro h
        subst q2
        rw [hq1] at hq2
        omega
      have hadj := ha4adj q2
      let p42 : sharpOuterplanarGraph.Walk 4 2 :=
        (model.route hadj).copy ha4 hq2
      rcases walk_right_to_left_hits p42 (by decide) (by decide) with
        ⟨w, hwsupport, hw⟩
      have hwsupport' : w ∈ (model.route hadj).support := by
        simpa [p42] using hwsupport
      rcases hw with rfl | rfl
      · apply branch_not_mem_route_support model hadj
          (c := a0) ha04 (ha0right q2)
        rw [ha0]
        exact hwsupport'
      · apply branch_not_mem_route_support model hadj
          (c := Sum.inr q1) (by
            exact fun h => ha4right q1 h.symm) (by
            simpa using hq12)
        rw [hq1]
        exact hwsupport'
    have hmust :
        rightHas 3 ∧ rightHas 5 := by
      have hfinite :
          ∀ r0 r1 r2 : Fin 6,
            (r0 ≠ r1 ∧ r0 ≠ r2 ∧ r1 ≠ r2 ∧
              r0 ≠ 0 ∧ r1 ≠ 0 ∧ r2 ≠ 0 ∧
              r0 ≠ 4 ∧ r1 ≠ 4 ∧ r2 ≠ 4 ∧
              ¬((r0 = 1 ∨ r1 = 1 ∨ r2 = 1) ∧
                (r0 = 2 ∨ r1 = 2 ∨ r2 = 2))) →
            (r0 = 3 ∨ r1 = 3 ∨ r2 = 3) ∧
              (r0 = 5 ∨ r1 = 5 ∨ r2 = 5) := by
        decide
      exact hfinite r0 r1 r2 ⟨hr01, hr02, hr12,
        hr0ne0, hr1ne0, hr2ne0, hr0ne4, hr1ne4, hr2ne4, hnotBoth⟩
    obtain ⟨q3, hq3⟩ := rightPreimage hmust.1
    obtain ⟨q5, hq5⟩ := rightPreimage hmust.2
    have hq35 : q3 ≠ q5 := by
      intro h
      subst q5
      rw [hq3] at hq5
      omega
    have hadj := ha0adj q5
    let p05 : sharpOuterplanarGraph.Walk 0 5 :=
      (model.route hadj).copy ha0 hq5
    rcases walk_left_to_right_hits p05 (by decide) (by decide) with
      ⟨w, hwsupport, hw⟩
    have hwsupport' : w ∈ (model.route hadj).support := by
      simpa [p05] using hwsupport
    rcases hw with rfl | rfl
    · apply branch_not_mem_route_support model hadj
        (c := Sum.inr q3) (by
          exact fun h => ha0right q3 h.symm) (by
          simpa using hq35)
      rw [hq3]
      exact hwsupport'
    · apply branch_not_mem_route_support model hadj
        (c := a4) ha04.symm (ha4right q5)
      rw [ha4]
      exact hwsupport'
  have impossible13
      (a1 a3 : Sum (Fin 2) (Fin 3))
      (ha1 : model.branch a1 = 1) (ha3 : model.branch a3 = 3)
      (ha1right : ∀ q : Fin 3, a1 ≠ Sum.inr q)
      (ha3right : ∀ q : Fin 3, a3 ≠ Sum.inr q)
      (ha13 : a1 ≠ a3)
      (ha1adj :
        ∀ q : Fin 3,
          (completeBipartiteGraph (Fin 2) (Fin 3)).Adj a1 (Sum.inr q))
      (ha3adj :
        ∀ q : Fin 3,
          (completeBipartiteGraph (Fin 2) (Fin 3)).Adj a3 (Sum.inr q)) :
      False := by
    let r0 := model.branch (Sum.inr (0 : Fin 3))
    let r1 := model.branch (Sum.inr (1 : Fin 3))
    let r2 := model.branch (Sum.inr (2 : Fin 3))
    have hr01 : r0 ≠ r1 := by
      intro h
      have := model.branch.injective h
      simp [r0, r1] at this
    have hr02 : r0 ≠ r2 := by
      intro h
      have := model.branch.injective h
      simp [r0, r2] at this
    have hr12 : r1 ≠ r2 := by
      intro h
      have := model.branch.injective h
      simp [r1, r2] at this
    let rightHas (v : Fin 6) : Prop := r0 = v ∨ r1 = v ∨ r2 = v
    have rightPreimage {v : Fin 6} (hv : rightHas v) :
        ∃ q : Fin 3, model.branch (Sum.inr q) = v := by
      rcases hv with h | h | h
      · exact ⟨0, by simpa [r0] using h⟩
      · exact ⟨1, by simpa [r1] using h⟩
      · exact ⟨2, by simpa [r2] using h⟩
    have hr0ne1 : r0 ≠ 1 := by
      intro h
      apply ha1right 0
      apply model.branch.injective
      simpa [r0] using ha1.trans h.symm
    have hr1ne1 : r1 ≠ 1 := by
      intro h
      apply ha1right 1
      apply model.branch.injective
      simpa [r1] using ha1.trans h.symm
    have hr2ne1 : r2 ≠ 1 := by
      intro h
      apply ha1right 2
      apply model.branch.injective
      simpa [r2] using ha1.trans h.symm
    have hr0ne3 : r0 ≠ 3 := by
      intro h
      apply ha3right 0
      apply model.branch.injective
      simpa [r0] using ha3.trans h.symm
    have hr1ne3 : r1 ≠ 3 := by
      intro h
      apply ha3right 1
      apply model.branch.injective
      simpa [r1] using ha3.trans h.symm
    have hr2ne3 : r2 ≠ 3 := by
      intro h
      apply ha3right 2
      apply model.branch.injective
      simpa [r2] using ha3.trans h.symm
    have hnotBoth : ¬(rightHas 0 ∧ rightHas 2) := by
      rintro ⟨hzero, htwo⟩
      obtain ⟨q0, hq0⟩ := rightPreimage hzero
      obtain ⟨q2, hq2⟩ := rightPreimage htwo
      have hq02 : q0 ≠ q2 := by
        intro h
        subst q2
        rw [hq0] at hq2
        omega
      have hadj := ha3adj q2
      let p32 : sharpOuterplanarGraph.Walk 3 2 :=
        (model.route hadj).copy ha3 hq2
      rcases walk_right_to_left_hits p32 (by decide) (by decide) with
        ⟨w, hwsupport, hw⟩
      have hwsupport' : w ∈ (model.route hadj).support := by
        simpa [p32] using hwsupport
      rcases hw with rfl | rfl
      · apply branch_not_mem_route_support model hadj
          (c := Sum.inr q0) (by
            exact fun h => ha3right q0 h.symm) (by
            simpa using hq02)
        rw [hq0]
        exact hwsupport'
      · apply branch_not_mem_route_support model hadj
          (c := a1) ha13 (ha1right q2)
        rw [ha1]
        exact hwsupport'
    have hmust :
        rightHas 4 ∧ rightHas 5 := by
      have hfinite :
          ∀ r0 r1 r2 : Fin 6,
            (r0 ≠ r1 ∧ r0 ≠ r2 ∧ r1 ≠ r2 ∧
              r0 ≠ 1 ∧ r1 ≠ 1 ∧ r2 ≠ 1 ∧
              r0 ≠ 3 ∧ r1 ≠ 3 ∧ r2 ≠ 3 ∧
              ¬((r0 = 0 ∨ r1 = 0 ∨ r2 = 0) ∧
                (r0 = 2 ∨ r1 = 2 ∨ r2 = 2))) →
            (r0 = 4 ∨ r1 = 4 ∨ r2 = 4) ∧
              (r0 = 5 ∨ r1 = 5 ∨ r2 = 5) := by
        decide
      exact hfinite r0 r1 r2 ⟨hr01, hr02, hr12,
        hr0ne1, hr1ne1, hr2ne1, hr0ne3, hr1ne3, hr2ne3, hnotBoth⟩
    obtain ⟨q4, hq4⟩ := rightPreimage hmust.1
    obtain ⟨q5, hq5⟩ := rightPreimage hmust.2
    have hq45 : q4 ≠ q5 := by
      intro h
      subst q5
      rw [hq4] at hq5
      omega
    have hadj := ha1adj q5
    let p15 : sharpOuterplanarGraph.Walk 1 5 :=
      (model.route hadj).copy ha1 hq5
    rcases walk_left_to_right_hits p15 (by decide) (by decide) with
      ⟨w, hwsupport, hw⟩
    have hwsupport' : w ∈ (model.route hadj).support := by
      simpa [p15] using hwsupport
    rcases hw with rfl | rfl
    · apply branch_not_mem_route_support model hadj
        (c := a3) ha13.symm (ha3right q5)
      rw [ha3]
      exact hwsupport'
    · apply branch_not_mem_route_support model hadj
        (c := Sum.inr q4) (by
          exact fun h => ha1right q4 h.symm) (by
          simpa using hq45)
      rw [hq4]
      exact hwsupport'
  rcases hopposite with h04 | h40 | h13 | h31
  · exact impossible04 left0 left1 h04.1 h04.2
      (by simp [left0]) (by simp [left1]) (by simp [left0, left1])
      (by intro q; simp [left0]) (by intro q; simp [left1])
  · exact impossible04 left1 left0 h40.2 h40.1
      (by simp [left1]) (by simp [left0]) (by simp [left0, left1])
      (by intro q; simp [left1]) (by intro q; simp [left0])
  · exact impossible13 left0 left1 h13.1 h13.2
      (by simp [left0]) (by simp [left1]) (by simp [left0, left1])
      (by intro q; simp [left0]) (by intro q; simp [left1])
  · exact impossible13 left1 left0 h31.2 h31.1
      (by simp [left1]) (by simp [left0]) (by simp [left0, left1])
      (by intro q; simp [left1]) (by intro q; simp [left0])

lemma sharpOuterplanarGraph_isOuterplanar :
    IsOuterplanar sharpOuterplanarGraph :=
  ⟨no_topological_K4, no_topological_K23⟩

/--
The two forbidden topological models are excluded directly using the
degree-three branch vertices and explicit vertex separators of the graph.
An explicit positive width-two map proves both upper bounds, while four
singleton symmetric differences and four cross-pair constraints rule out
every ordinary width-one no-clash map.
-/
theorem outerplanar_bound_is_sharp :
    IsOuterplanar sharpOuterplanarGraph ∧
    nctd sharpOuterplanarGraph 1 = 2 ∧
    positiveNCTD sharpOuterplanarGraph 1 = 2 :=
  ⟨sharpOuterplanarGraph_isOuterplanar, nctd_sharp_values⟩

/--
---
conclusion: Lax16.OuterplanarSharpness.positiveNCTD_ge_two
---
The explicit outerplanar example and the lower half of its exact dimension
calculation give the required sharpness witness.
-/
theorem positiveNCTD_ge_two :
    IsOuterplanar sharpOuterplanarGraph ∧
      2 ≤ positiveNCTD sharpOuterplanarGraph 1 :=
  ⟨sharpOuterplanarGraph_isOuterplanar,
    by rw [outerplanar_bound_is_sharp.2.2]⟩

end Lax16Proofs.OuterplanarSharpness
