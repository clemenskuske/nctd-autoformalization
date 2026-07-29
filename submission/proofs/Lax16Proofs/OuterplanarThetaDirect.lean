import Lax16.PlanarGraphs
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Internal theta-model and rotation infrastructure for the outerplanar block proof. -/

namespace Lax16Proofs
namespace Lax16ThetaDirect

open Lax16.PlanarGraphs

universe u

/-- The strong theta invariant used below. -/
structure ThetaModel {V : Type u} (G : SimpleGraph V) where
  left : V
  right : V
  endpoints_ne : left ≠ right
  route : Fin 3 → G.Walk left right
  route_isPath : ∀ i, (route i).IsPath
  route_snd_injective : Function.Injective fun i => (route i).snd
  interiors_disjoint :
    ∀ i j, i ≠ j →
      Disjoint (walkInterior (route i)) (walkInterior (route j))

namespace ThetaModel

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

def vertexSet (T : ThetaModel G) : Set V :=
  {z | ∃ i : Fin 3, z ∈ (T.route i).support}

noncomputable def vertices (T : ThetaModel G) : Finset V := by
  classical
  exact Finset.univ.filter fun z => z ∈ T.vertexSet

noncomputable def size (T : ThetaModel G) : ℕ := T.vertices.card

def span (T : ThetaModel G) : ℕ :=
  max (T.route 0).length
    (max (T.route 1).length (T.route 2).length)

noncomputable def rank (T : ThetaModel G) : ℕ :=
  T.size * (Fintype.card V + 1) + T.span

theorem mem_vertices_iff (T : ThetaModel G) {z : V} :
    z ∈ T.vertices ↔ z ∈ T.vertexSet := by
  classical
  simp [vertices]

theorem route_support_subset_vertexSet (T : ThetaModel G) (i : Fin 3) :
    {z | z ∈ (T.route i).support} ⊆ T.vertexSet :=
  fun _ hz => ⟨i, hz⟩

theorem left_mem_vertexSet (T : ThetaModel G) :
    T.left ∈ T.vertexSet :=
  ⟨0, (T.route 0).start_mem_support⟩

theorem right_mem_vertexSet (T : ThetaModel G) :
    T.right ∈ T.vertexSet :=
  ⟨0, (T.route 0).end_mem_support⟩

theorem size_le_card (T : ThetaModel G) :
    T.size ≤ Fintype.card V := by
  classical
  exact Finset.card_le_univ T.vertices

theorem route_length_le_span (T : ThetaModel G) (i : Fin 3) :
    (T.route i).length ≤ T.span := by
  fin_cases i <;> simp [span]

theorem span_lt_card (T : ThetaModel G) :
    T.span < Fintype.card V := by
  simp only [span, max_lt_iff]
  exact ⟨(T.route_isPath 0).length_lt,
    (T.route_isPath 1).length_lt,
    (T.route_isPath 2).length_lt⟩

theorem rank_lt_bound (T : ThetaModel G) :
    T.rank < (Fintype.card V + 1) * (Fintype.card V + 1) := by
  unfold rank
  have hs := T.size_le_card
  have hp := T.span_lt_card
  nlinarith

/-- A finite graph has a strong theta maximal for support/span rank. -/
theorem exists_rank_maximal (T₀ : ThetaModel G) :
    ∃ T : ThetaModel G, ∀ T' : ThetaModel G, T'.rank ≤ T.rank := by
  classical
  let bound := (Fintype.card V + 1) * (Fintype.card V + 1)
  let achievable : Finset ℕ :=
    (Finset.range bound).filter fun n =>
      ∃ T : ThetaModel G, T.rank = n
  have hT₀ : T₀.rank ∈ achievable := by
    simp only [achievable, Finset.mem_filter, Finset.mem_range]
    exact ⟨T₀.rank_lt_bound, ⟨T₀, rfl⟩⟩
  have hne : achievable.Nonempty := ⟨T₀.rank, hT₀⟩
  let m := achievable.max' hne
  have hm : m ∈ achievable := achievable.max'_mem hne
  obtain ⟨T, hTrank⟩ :
      ∃ T : ThetaModel G, T.rank = m := (Finset.mem_filter.mp hm).2
  refine ⟨T, fun T' => ?_⟩
  rw [hTrank]
  apply Finset.le_max' achievable
  simp only [achievable, Finset.mem_filter, Finset.mem_range]
  exact ⟨T'.rank_lt_bound, ⟨T', rfl⟩⟩

/-- Strictly more support beats every possible span loss. -/
theorem rank_lt_of_size_lt
    (T T' : ThetaModel G) (hsize : T.size < T'.size) :
    T.rank < T'.rank := by
  unfold rank
  have hspan := T.span_lt_card
  have hmul :
      (T.size + 1) * (Fintype.card V + 1) ≤
        T'.size * (Fintype.card V + 1) :=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hsize)
  calc
    T.size * (Fintype.card V + 1) + T.span
        < T.size * (Fintype.card V + 1) +
            (Fintype.card V + 1) := by omega
    _ = (T.size + 1) * (Fintype.card V + 1) := by
      rw [Nat.add_mul]
      simp
    _ ≤ T'.size * (Fintype.card V + 1) := hmul
    _ ≤ T'.size * (Fintype.card V + 1) + T'.span :=
      Nat.le_add_right _ _

/-- At equal support size, rank comparison is exactly span comparison. -/
theorem rank_lt_of_size_eq_of_span_lt
    (T T' : ThetaModel G) (hsize : T.size = T'.size)
    (hspan : T.span < T'.span) :
    T.rank < T'.rank := by
  unfold rank
  rw [hsize]
  exact Nat.add_lt_add_left hspan _

theorem size_eq_of_vertexSet_eq (T T' : ThetaModel G)
    (h : T.vertexSet = T'.vertexSet) :
    T.size = T'.size := by
  classical
  unfold size vertices
  congr 1
  ext z
  simp [h]

theorem size_lt_of_vertexSet_ssubset (T T' : ThetaModel G)
    (h : T.vertexSet ⊂ T'.vertexSet) :
    T.size < T'.size := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro z hz
    rw [T.mem_vertices_iff] at hz
    rw [T'.mem_vertices_iff]
    exact h.1 hz
  · intro heq
    apply h.2
    intro z hz
    rw [← T.mem_vertices_iff, heq, T'.mem_vertices_iff]
    exact hz

theorem size_lt_of_vertexSet_subset_of_new
    (T T' : ThetaModel G)
    (hsub : T.vertexSet ⊆ T'.vertexSet)
    {z : V} (hznew : z ∉ T.vertexSet) (hzmem : z ∈ T'.vertexSet) :
    T.size < T'.size := by
  apply T.size_lt_of_vertexSet_ssubset T'
  refine ⟨hsub, ?_⟩
  intro hreverse
  exact hznew (hreverse hzmem)

/-- A rank-maximal theta cannot be replaced by one covering a new vertex. -/
theorem not_vertexSet_subset_of_rank_maximal
    (T : ThetaModel G)
    (hmax : ∀ T' : ThetaModel G, T'.rank ≤ T.rank)
    (T' : ThetaModel G)
    (hsub : T.vertexSet ⊆ T'.vertexSet)
    {z : V} (hznew : z ∉ T.vertexSet) (hzmem : z ∈ T'.vertexSet) :
    False := by
  have hs : T.size < T'.size :=
    T.size_lt_of_vertexSet_subset_of_new T' hsub hznew hzmem
  exact (not_lt_of_ge (hmax T')) (rank_lt_of_size_lt T T' hs)

/-- A rank-maximal theta cannot have an equal-support replacement with a
route longer than the old span. -/
theorem not_longer_route_of_rank_maximal
    (T : ThetaModel G)
    (hmax : ∀ T' : ThetaModel G, T'.rank ≤ T.rank)
    (T' : ThetaModel G)
    (hvertices : T.vertexSet = T'.vertexSet)
    (i : Fin 3) (hlong : T.span < (T'.route i).length) :
    False := by
  have hsize := T.size_eq_of_vertexSet_eq T' hvertices
  have hspan : T.span < T'.span :=
    hlong.trans_le (T'.route_length_le_span i)
  exact (not_lt_of_ge (hmax T'))
    (rank_lt_of_size_eq_of_span_lt T T' hsize hspan)

end ThetaModel

/-- A path whose endpoints are on a theta and whose interior is outside it. -/
structure ThetaEar {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : ThetaModel G) where
  start : V
  stop : V
  endpoints_ne : start ≠ stop
  start_mem : start ∈ T.vertexSet
  stop_mem : stop ∈ T.vertexSet
  route : G.Walk start stop
  route_isPath : route.IsPath
  interior_avoids :
    Disjoint (walkInterior route) T.vertexSet

namespace ThetaEar

variable {V : Type u} [Fintype V] {G : SimpleGraph V}
    {T : ThetaModel G}

/-- An ear interior is disjoint from any walk whose interior lies in the
old theta. -/
theorem disjoint_walkInterior_of_subset (E : ThetaEar T)
    {a b : V} (p : G.Walk a b)
    (hp : walkInterior p ⊆ T.vertexSet) :
    Disjoint (walkInterior E.route) (walkInterior p) := by
  exact E.interior_avoids.mono_right hp

end ThetaEar

/-- Two simple paths sharing only their glued endpoint append to a path. -/
theorem isPath_append_of_eq_endpoint
    {V : Type u} {G : SimpleGraph V} {a b c : V}
    (p : G.Walk a b) (q : G.Walk b c)
    (hp : p.IsPath) (hq : q.IsPath)
    (hcommon :
      ∀ x, x ∈ p.support → x ∈ q.support → x = b) :
    (p.append q).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
  apply List.nodup_append.mpr
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  intro x hxp y hyqtail hxy
  subst y
  have hxq : x ∈ q.support := List.mem_of_mem_tail hyqtail
  have hxb : x = b := hcommon x hxp hxq
  subst x
  cases q with
  | nil => simp at hyqtail
  | cons h r =>
      exact ((SimpleGraph.Walk.cons_isPath_iff h r).mp hq).2 hyqtail

/-- A prefix ending at an internal point has interior in the old interior. -/
theorem walkInterior_takeUntil_subset
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {a b x : V} (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∈ walkInterior p) :
    walkInterior (p.takeUntil x hx.1) ⊆ walkInterior p := by
  intro z hz
  refine ⟨p.support_takeUntil_subset_support hx.1 hz.1, hz.2.1, ?_⟩
  intro hzb
  apply (SimpleGraph.Walk.endpoint_notMem_support_takeUntil hp hx.1 hx.2.2.symm)
  subst z
  exact hz.1

/-- A suffix beginning at an internal point has interior in the old interior. -/
theorem walkInterior_dropUntil_subset
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {a b x : V} (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∈ walkInterior p) :
    walkInterior (p.dropUntil x hx.1) ⊆ walkInterior p := by
  intro z hz
  refine ⟨p.support_dropUntil_subset hx.1 hz.1, ?_, hz.2.2⟩
  intro hza
  have ha_take : a ∈ (p.takeUntil x hx.1).support :=
    (p.takeUntil x hx.1).start_mem_support
  have ha_drop : a ∈ (p.dropUntil x hx.1).support := by
    subst z
    exact hz.1
  have hpath : ((p.takeUntil x hx.1).append
      (p.dropUntil x hx.1)).IsPath := by simpa using hp
  have hcommon := hpath.ne_of_mem_support_of_append
    hx.2.1.symm ha_take ha_drop
  exact hcommon rfl

theorem walkInterior_reverse
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) :
    walkInterior p.reverse = walkInterior p := by
  ext z
  simp only [walkInterior, Set.mem_setOf_eq,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  tauto

/-- Once a path is cut at a non-start vertex, its original start does not
occur in the suffix. -/
theorem start_not_mem_dropUntil
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {a b x : V} (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∈ p.support) (hax : a ≠ x) :
    a ∉ (p.dropUntil x hx).support := by
  intro ha
  have hsplit : ((p.takeUntil x hx).append
      (p.dropUntil x hx)).IsPath := by simpa using hp
  exact hsplit.ne_of_mem_support_of_append hax
    (p.takeUntil x hx).start_mem_support ha rfl

/-- Distinct theta routes can meet only at their two common endpoints. -/
theorem eq_endpoint_of_mem_two_theta_routes
    {V : Type u} {G : SimpleGraph V}
    (T : ThetaModel G) {i j : Fin 3} (hij : i ≠ j)
    {z : V} (hzi : z ∈ (T.route i).support)
    (hzj : z ∈ (T.route j).support) :
    z = T.left ∨ z = T.right := by
  by_cases hzleft : z = T.left
  · exact Or.inl hzleft
  by_cases hzright : z = T.right
  · exact Or.inr hzright
  exfalso
  exact Set.disjoint_left.mp (T.interiors_disjoint i j hij)
    ⟨hzi, hzleft, hzright⟩ ⟨hzj, hzleft, hzright⟩

/-- The complementary `x`-to-`z` route used in the same-arm rotation:
go back to the left theta endpoint, traverse another arm, then return from
the right endpoint along the suffix of the original arm. -/
noncomputable def sameArmDetour
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G) (i j : Fin 3)
    {x z : V} (hx : x ∈ (T.route i).support)
    (hzAfter : z ∈ ((T.route i).dropUntil x hx).support) :
    G.Walk x z := by
  classical
  let beforeX := (T.route i).takeUntil x hx
  let afterX := (T.route i).dropUntil x hx
  let afterZ := afterX.dropUntil z hzAfter
  exact (beforeX.reverse.append (T.route j)).append afterZ.reverse

/-- The complementary route in a same-arm rotation is simple. -/
theorem sameArmDetour_isPath
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G) {i j : Fin 3} (hij : i ≠ j)
    {x z : V} (hx : x ∈ walkInterior (T.route i))
    (hzAfter : z ∈ ((T.route i).dropUntil x hx.1).support)
    (hxz : x ≠ z) :
    (sameArmDetour T i j hx.1 hzAfter).IsPath := by
  classical
  let p := T.route i
  let q := T.route j
  let beforeX := p.takeUntil x hx.1
  let afterX := p.dropUntil x hx.1
  let afterZ := afterX.dropUntil z hzAfter
  have hbefore : beforeX.IsPath := (T.route_isPath i).takeUntil hx.1
  have hafterX : afterX.IsPath := (T.route_isPath i).dropUntil hx.1
  have hafterZ : afterZ.IsPath := hafterX.dropUntil hzAfter
  have hfirst : (beforeX.reverse.append q).IsPath := by
    apply isPath_append_of_eq_endpoint beforeX.reverse q
      hbefore.reverse (T.route_isPath j)
    intro y hybefore hyq
    have hyp : y ∈ p.support := by
      apply p.support_takeUntil_subset_support hx.1
      simpa [beforeX] using hybefore
    rcases eq_endpoint_of_mem_two_theta_routes T hij hyp hyq with
      hyleft | hyright
    · exact hyleft
    · exfalso
      have hrightBefore : T.right ∈ beforeX.support := by
        simpa [beforeX, SimpleGraph.Walk.support_reverse, hyright] using
          hybefore
      exact (SimpleGraph.Walk.endpoint_notMem_support_takeUntil
        (T.route_isPath i) hx.1 hx.2.2.symm) hrightBefore
  have hsecond :
      ((beforeX.reverse.append q).append afterZ.reverse).IsPath := by
    apply isPath_append_of_eq_endpoint (beforeX.reverse.append q)
      afterZ.reverse hfirst hafterZ.reverse
    intro y hyfirst hyafter
    have hyafterZ : y ∈ afterZ.support := by
      simpa [afterZ] using hyafter
    have hyafterX : y ∈ afterX.support :=
      afterX.support_dropUntil_subset hzAfter hyafterZ
    rw [SimpleGraph.Walk.mem_support_append_iff] at hyfirst
    rcases hyfirst with hybefore | hyq
    · have hybefore' : y ∈ beforeX.support := by
        simpa [beforeX] using hybefore
      by_cases hyx : y = x
      · subst y
        exact False.elim <|
          start_not_mem_dropUntil afterX hafterX hzAfter hxz hyafterZ
      · have hsplit : (beforeX.append afterX).IsPath := by
          simpa [beforeX, afterX, p] using T.route_isPath i
        exact False.elim <|
          hsplit.ne_of_mem_support_of_append hyx
            hybefore' hyafterX rfl
    · have hyp : y ∈ p.support :=
        p.support_dropUntil_subset hx.1 hyafterX
      rcases eq_endpoint_of_mem_two_theta_routes T hij hyp hyq with
        hyleft | hyright
      · subst y
        exact False.elim <|
          start_not_mem_dropUntil p (T.route_isPath i) hx.1
            hx.2.1.symm hyafterX
      · exact hyright
  simpa [sameArmDetour, beforeX, afterX, afterZ, p, q] using hsecond

/-- The two halves of a path split at `x` have disjoint interiors. -/
theorem disjoint_walkInterior_takeUntil_dropUntil
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {a b x : V} (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∈ p.support) :
    Disjoint (walkInterior (p.takeUntil x hx))
      (walkInterior (p.dropUntil x hx)) := by
  apply Set.disjoint_left.mpr
  intro z hzt hzd
  have hpath : ((p.takeUntil x hx).append
      (p.dropUntil x hx)).IsPath := by simpa using hp
  exact hpath.ne_of_mem_support_of_append
    hzd.2.1 hzt.1 hzd.1 rfl

/-- Package three concrete paths as a strong theta.  Pairwise first-vertex
inequalities are exactly the strengthened invariant needed later. -/
def thetaModelOfThreePaths
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : a ≠ b)
    (p₀ p₁ p₂ : G.Walk a b)
    (hp₀ : p₀.IsPath) (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (h01snd : p₀.snd ≠ p₁.snd)
    (h02snd : p₀.snd ≠ p₂.snd)
    (h12snd : p₁.snd ≠ p₂.snd)
    (h01 : Disjoint (walkInterior p₀) (walkInterior p₁))
    (h02 : Disjoint (walkInterior p₀) (walkInterior p₂))
    (h12 : Disjoint (walkInterior p₁) (walkInterior p₂)) :
    ThetaModel G where
  left := a
  right := b
  endpoints_ne := hab
  route := ![p₀, p₁, p₂]
  route_isPath i := by
    fin_cases i <;> simp [hp₀, hp₁, hp₂]
  route_snd_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  interiors_disjoint := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Disjoint.symm]

@[simp] theorem thetaModelOfThreePaths_route_zero
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : a ≠ b) (p₀ p₁ p₂ : G.Walk a b)
    (hp₀ hp₁ hp₂) (h01snd h02snd h12snd) (h01 h02 h12) :
    (thetaModelOfThreePaths hab p₀ p₁ p₂
      hp₀ hp₁ hp₂ h01snd h02snd h12snd h01 h02 h12).route 0 = p₀ := rfl

@[simp] theorem thetaModelOfThreePaths_route_one
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : a ≠ b) (p₀ p₁ p₂ : G.Walk a b)
    (hp₀ hp₁ hp₂) (h01snd h02snd h12snd) (h01 h02 h12) :
    (thetaModelOfThreePaths hab p₀ p₁ p₂
      hp₀ hp₁ hp₂ h01snd h02snd h12snd h01 h02 h12).route 1 = p₁ := rfl

@[simp] theorem thetaModelOfThreePaths_route_two
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : a ≠ b) (p₀ p₁ p₂ : G.Walk a b)
    (hp₀ hp₁ hp₂) (h01snd h02snd h12snd) (h01 h02 h12) :
    (thetaModelOfThreePaths hab p₀ p₁ p₂
      hp₀ hp₁ hp₂ h01snd h02snd h12snd h01 h02 h12).route 2 = p₂ := rfl

/-- The segment from `x` to the later point `z` on the same arm. -/
noncomputable def sameArmSegment
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G) (i : Fin 3)
    {x z : V} (hx : x ∈ (T.route i).support)
    (hzAfter : z ∈ ((T.route i).dropUntil x hx).support) :
    G.Walk x z :=
  ((T.route i).dropUntil x hx).takeUntil z hzAfter

theorem sameArmSegment_isPath
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G) (i : Fin 3)
    {x z : V} (hx : x ∈ (T.route i).support)
    (hzAfter : z ∈ ((T.route i).dropUntil x hx).support) :
    (sameArmSegment T i hx hzAfter).IsPath := by
  exact ((T.route_isPath i).dropUntil hx).takeUntil hzAfter

theorem sameArmSegment_interior_subset_vertexSet
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G) (i : Fin 3)
    {x z : V} (hx : x ∈ (T.route i).support)
    (hzAfter : z ∈ ((T.route i).dropUntil x hx).support) :
    walkInterior (sameArmSegment T i hx hzAfter) ⊆ T.vertexSet := by
  intro y hy
  refine ⟨i, ?_⟩
  apply (T.route i).support_dropUntil_subset hx
  apply ((T.route i).dropUntil x hx).support_takeUntil_subset_support
    hzAfter
  exact hy.1

theorem sameArmDetour_interior_subset_vertexSet
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G) (i j : Fin 3)
    {x z : V} (hx : x ∈ (T.route i).support)
    (hzAfter : z ∈ ((T.route i).dropUntil x hx).support) :
    walkInterior (sameArmDetour T i j hx hzAfter) ⊆ T.vertexSet := by
  intro y hy
  let p := T.route i
  let beforeX := p.takeUntil x hx
  let afterX := p.dropUntil x hx
  let afterZ := afterX.dropUntil z hzAfter
  have hyd :
      y ∈ ((beforeX.reverse.append (T.route j)).append
        afterZ.reverse).support := by
    simpa [sameArmDetour, beforeX, afterX, afterZ, p] using hy.1
  rw [SimpleGraph.Walk.mem_support_append_iff] at hyd
  rcases hyd with hyfirst | hyafter
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hyfirst
    rcases hyfirst with hybefore | hyj
    · refine ⟨i, ?_⟩
      apply p.support_takeUntil_subset_support hx
      simpa [beforeX] using hybefore
    · exact ⟨j, hyj⟩
  · refine ⟨i, ?_⟩
    apply p.support_dropUntil_subset hx
    apply afterX.support_dropUntil_subset hzAfter
    simpa [afterZ] using hyafter

/-- The on-arm segment and the complementary route are internally
disjoint; this is the central local verification in the same-arm case. -/
theorem sameArmSegment_disjoint_detour
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G) {i j : Fin 3} (hij : i ≠ j)
    {x z : V} (hx : x ∈ walkInterior (T.route i))
    (hzAfter : z ∈ ((T.route i).dropUntil x hx.1).support)
    (hxz : x ≠ z) :
    Disjoint
      (walkInterior (sameArmSegment T i hx.1 hzAfter))
      (walkInterior (sameArmDetour T i j hx.1 hzAfter)) := by
  classical
  let p := T.route i
  let q := T.route j
  let beforeX := p.takeUntil x hx.1
  let afterX := p.dropUntil x hx.1
  let middle := afterX.takeUntil z hzAfter
  let afterZ := afterX.dropUntil z hzAfter
  have hp : p.IsPath := T.route_isPath i
  have hafterX : afterX.IsPath := hp.dropUntil hx.1
  have hsplitX : (beforeX.append afterX).IsPath := by
    simpa [beforeX, afterX, p] using hp
  have hsplitZ : (middle.append afterZ).IsPath := by
    simpa [middle, afterZ, afterX] using hafterX
  apply Set.disjoint_left.mpr
  intro y hymid hydetour
  have hymiddle : y ∈ middle.support := by
    simpa [sameArmSegment, middle, afterX, p] using hymid.1
  have hyafterX : y ∈ afterX.support :=
    afterX.support_takeUntil_subset_support hzAfter hymiddle
  have hyp : y ∈ p.support :=
    p.support_dropUntil_subset hx.1 hyafterX
  have hyd :
      y ∈ ((beforeX.reverse.append q).append afterZ.reverse).support := by
    simpa [sameArmDetour, beforeX, afterX, afterZ, p, q] using
      hydetour.1
  rw [SimpleGraph.Walk.mem_support_append_iff] at hyd
  rcases hyd with hyfirst | hyafterZ
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hyfirst
    rcases hyfirst with hybefore | hyq
    · have hybefore' : y ∈ beforeX.support := by
        simpa [beforeX] using hybefore
      exact hsplitX.ne_of_mem_support_of_append
        hymid.2.1 hybefore' hyafterX rfl
    · have hyleft : y ≠ T.left := by
        intro h
        subst y
        exact start_not_mem_dropUntil p hp hx.1 hx.2.1.symm hyafterX
      have hyright : y ≠ T.right := by
        intro h
        subst y
        by_cases hzr : z = T.right
        · exact hymid.2.2 hzr.symm
        · exact (SimpleGraph.Walk.endpoint_notMem_support_takeUntil
            hafterX hzAfter (Ne.symm hzr)) hymiddle
      exact Set.disjoint_left.mp (T.interiors_disjoint i j hij)
        ⟨hyp, hyleft, hyright⟩ ⟨hyq, hyleft, hyright⟩
  · have hyafterZ' : y ∈ afterZ.support := by
      simpa [afterZ] using hyafterZ
    exact hsplitZ.ne_of_mem_support_of_append
      hymid.2.2 hymiddle hyafterZ' rfl

/--
The public same-arm replacement constructor.  Its routes are, in order:
the new ear/chord, the old arm segment, and the complementary detour through
another theta arm.  The caller supplies only the genuinely local
first-vertex and interior-disjointness facts.
-/
noncomputable def sameArmRotatedTheta
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G) {i j : Fin 3} (hij : i ≠ j)
    {x z : V} (hx : x ∈ walkInterior (T.route i))
    (hzAfter : z ∈ ((T.route i).dropUntil x hx.1).support)
    (hxz : x ≠ z)
    (ear : G.Walk x z) (hear : ear.IsPath)
    (hsndEarSegment :
      ear.snd ≠ (sameArmSegment T i hx.1 hzAfter).snd)
    (hsndEarDetour :
      ear.snd ≠ (sameArmDetour T i j hx.1 hzAfter).snd)
    (hsndSegmentDetour :
      (sameArmSegment T i hx.1 hzAfter).snd ≠
        (sameArmDetour T i j hx.1 hzAfter).snd)
    (hEarSegment :
      Disjoint (walkInterior ear)
        (walkInterior (sameArmSegment T i hx.1 hzAfter)))
    (hEarDetour :
      Disjoint (walkInterior ear)
        (walkInterior (sameArmDetour T i j hx.1 hzAfter)))
    (hSegmentDetour :
      Disjoint (walkInterior (sameArmSegment T i hx.1 hzAfter))
        (walkInterior (sameArmDetour T i j hx.1 hzAfter))) :
    ThetaModel G :=
  thetaModelOfThreePaths hxz
    ear
    (sameArmSegment T i hx.1 hzAfter)
    (sameArmDetour T i j hx.1 hzAfter)
    hear
    (sameArmSegment_isPath T i hx.1 hzAfter)
    (sameArmDetour_isPath T hij hx hzAfter hxz)
    hsndEarSegment hsndEarDetour hsndSegmentDetour
    hEarSegment hEarDetour hSegmentDetour

/-- Same-arm constructor specialized to an ear whose interior avoids the
old theta; all three interior-disjointness obligations are discharged
internally. -/
noncomputable def sameArmRotatedThetaOfEar
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G) {i j : Fin 3} (hij : i ≠ j)
    {x z : V} (hx : x ∈ walkInterior (T.route i))
    (hzAfter : z ∈ ((T.route i).dropUntil x hx.1).support)
    (hxz : x ≠ z)
    (ear : G.Walk x z) (hear : ear.IsPath)
    (hEarAvoid : Disjoint (walkInterior ear) T.vertexSet)
    (hsndEarSegment :
      ear.snd ≠ (sameArmSegment T i hx.1 hzAfter).snd)
    (hsndEarDetour :
      ear.snd ≠ (sameArmDetour T i j hx.1 hzAfter).snd)
    (hsndSegmentDetour :
      (sameArmSegment T i hx.1 hzAfter).snd ≠
        (sameArmDetour T i j hx.1 hzAfter).snd) :
    ThetaModel G :=
  sameArmRotatedTheta T hij hx hzAfter hxz ear hear
    hsndEarSegment hsndEarDetour hsndSegmentDetour
    (hEarAvoid.mono_right
      (sameArmSegment_interior_subset_vertexSet T i hx.1 hzAfter))
    (hEarAvoid.mono_right
      (sameArmDetour_interior_subset_vertexSet T i j hx.1 hzAfter))
    (sameArmSegment_disjoint_detour T hij hx hzAfter hxz)

/--
Same-arm rotation contradicts rank maximality once the standard local
verification shows equal covered support and that the complementary detour
is longer than the old span.  This is the exact interface used by the final
direct-arm case split.
-/
theorem false_of_sameArmRotatedTheta
    {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G)
    (hmax : ∀ T' : ThetaModel G, T'.rank ≤ T.rank)
    {i j : Fin 3} (hij : i ≠ j)
    {x z : V} (hx : x ∈ walkInterior (T.route i))
    (hzAfter : z ∈ ((T.route i).dropUntil x hx.1).support)
    (hxz : x ≠ z)
    (ear : G.Walk x z) (hear : ear.IsPath)
    (hsndEarSegment :
      ear.snd ≠ (sameArmSegment T i hx.1 hzAfter).snd)
    (hsndEarDetour :
      ear.snd ≠ (sameArmDetour T i j hx.1 hzAfter).snd)
    (hsndSegmentDetour :
      (sameArmSegment T i hx.1 hzAfter).snd ≠
        (sameArmDetour T i j hx.1 hzAfter).snd)
    (hEarSegment :
      Disjoint (walkInterior ear)
        (walkInterior (sameArmSegment T i hx.1 hzAfter)))
    (hEarDetour :
      Disjoint (walkInterior ear)
        (walkInterior (sameArmDetour T i j hx.1 hzAfter)))
    (hSegmentDetour :
      Disjoint (walkInterior (sameArmSegment T i hx.1 hzAfter))
        (walkInterior (sameArmDetour T i j hx.1 hzAfter)))
    (hvertices :
      T.vertexSet =
        (sameArmRotatedTheta T hij hx hzAfter hxz ear hear
          hsndEarSegment hsndEarDetour hsndSegmentDetour
          hEarSegment hEarDetour hSegmentDetour).vertexSet)
    (hlong :
      T.span < (sameArmDetour T i j hx.1 hzAfter).length) :
    False := by
  let T' :=
    sameArmRotatedTheta T hij hx hzAfter hxz ear hear
      hsndEarSegment hsndEarDetour hsndSegmentDetour
      hEarSegment hEarDetour hSegmentDetour
  apply T.not_longer_route_of_rank_maximal hmax T' hvertices 2
  simpa [T'] using hlong

/-- The off-theta-ear variant: a single new interior vertex makes the
rotated theta strictly larger, so no span comparison is needed. -/
theorem false_of_sameArmRotatedTheta_new_vertex
    {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G)
    (hmax : ∀ T' : ThetaModel G, T'.rank ≤ T.rank)
    {i j : Fin 3} (hij : i ≠ j)
    {x z : V} (hx : x ∈ walkInterior (T.route i))
    (hzAfter : z ∈ ((T.route i).dropUntil x hx.1).support)
    (hxz : x ≠ z)
    (ear : G.Walk x z) (hear : ear.IsPath)
    (hsndEarSegment :
      ear.snd ≠ (sameArmSegment T i hx.1 hzAfter).snd)
    (hsndEarDetour :
      ear.snd ≠ (sameArmDetour T i j hx.1 hzAfter).snd)
    (hsndSegmentDetour :
      (sameArmSegment T i hx.1 hzAfter).snd ≠
        (sameArmDetour T i j hx.1 hzAfter).snd)
    (hEarSegment :
      Disjoint (walkInterior ear)
        (walkInterior (sameArmSegment T i hx.1 hzAfter)))
    (hEarDetour :
      Disjoint (walkInterior ear)
        (walkInterior (sameArmDetour T i j hx.1 hzAfter)))
    (hSegmentDetour :
      Disjoint (walkInterior (sameArmSegment T i hx.1 hzAfter))
        (walkInterior (sameArmDetour T i j hx.1 hzAfter)))
    (hsub :
      T.vertexSet ⊆
        (sameArmRotatedTheta T hij hx hzAfter hxz ear hear
          hsndEarSegment hsndEarDetour hsndSegmentDetour
          hEarSegment hEarDetour hSegmentDetour).vertexSet)
    {y : V} (hynew : y ∉ T.vertexSet)
    (hyear :
      y ∈
        (sameArmRotatedTheta T hij hx hzAfter hxz ear hear
          hsndEarSegment hsndEarDetour hsndSegmentDetour
          hEarSegment hEarDetour hSegmentDetour).vertexSet) :
    False := by
  let T' :=
    sameArmRotatedTheta T hij hx hzAfter hxz ear hear
      hsndEarSegment hsndEarDetour hsndSegmentDetour
      hEarSegment hEarDetour hSegmentDetour
  exact T.not_vertexSet_subset_of_rank_maximal
    hmax T' hsub hynew hyear

/-- Complementary route for an ear that returns from `x` to the old left
theta endpoint: follow the suffix of arm `i` to the right endpoint, then
traverse arm `j` backwards. -/
noncomputable def leftReturnDetour
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G) (i j : Fin 3)
    {x : V} (hx : x ∈ (T.route i).support) :
    G.Walk x T.left :=
  ((T.route i).dropUntil x hx).append (T.route j).reverse

theorem leftReturnDetour_isPath
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G) {i j : Fin 3} (hij : i ≠ j)
    {x : V} (hx : x ∈ walkInterior (T.route i)) :
    (leftReturnDetour T i j hx.1).IsPath := by
  let p := T.route i
  let q := T.route j
  let afterX := p.dropUntil x hx.1
  apply isPath_append_of_eq_endpoint afterX q.reverse
    ((T.route_isPath i).dropUntil hx.1) (T.route_isPath j).reverse
  intro y hyafter hyq
  have hyp : y ∈ p.support :=
    p.support_dropUntil_subset hx.1 hyafter
  have hyq' : y ∈ q.support := by
    simpa [q, SimpleGraph.Walk.support_reverse] using hyq
  rcases eq_endpoint_of_mem_two_theta_routes T hij hyp hyq' with
    hyleft | hyright
  · subst y
    exact False.elim <|
      start_not_mem_dropUntil p (T.route_isPath i) hx.1
        hx.2.1.symm hyafter
  · exact hyright

theorem leftReturnPrefix_interior_subset_vertexSet
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G) (i : Fin 3)
    {x : V} (hx : x ∈ (T.route i).support) :
    walkInterior ((T.route i).takeUntil x hx).reverse ⊆
      T.vertexSet := by
  intro y hy
  refine ⟨i, ?_⟩
  apply (T.route i).support_takeUntil_subset_support hx
  simpa [SimpleGraph.Walk.support_reverse] using hy.1

theorem leftReturnDetour_interior_subset_vertexSet
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G) (i j : Fin 3)
    {x : V} (hx : x ∈ (T.route i).support) :
    walkInterior (leftReturnDetour T i j hx) ⊆ T.vertexSet := by
  intro y hy
  have hyd := hy.1
  rw [leftReturnDetour, SimpleGraph.Walk.mem_support_append_iff] at hyd
  rcases hyd with hyi | hyj
  · exact ⟨i, (T.route i).support_dropUntil_subset hx hyi⟩
  · exact ⟨j, by
      simpa [SimpleGraph.Walk.support_reverse] using hyj⟩

/-- The reversed prefix and the suffix-through-another-arm detour in the
left-return construction are internally disjoint. -/
theorem leftReturnPrefix_disjoint_detour
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G) {i j : Fin 3} (hij : i ≠ j)
    {x : V} (hx : x ∈ walkInterior (T.route i)) :
    Disjoint
      (walkInterior ((T.route i).takeUntil x hx.1).reverse)
      (walkInterior (leftReturnDetour T i j hx.1)) := by
  let p := T.route i
  let q := T.route j
  let beforeX := p.takeUntil x hx.1
  let afterX := p.dropUntil x hx.1
  have hsplit : (beforeX.append afterX).IsPath := by
    simpa [beforeX, afterX, p] using T.route_isPath i
  apply Set.disjoint_left.mpr
  intro y hybefore hydetour
  have hybefore' : y ∈ beforeX.support := by
    simpa [beforeX, SimpleGraph.Walk.support_reverse] using hybefore.1
  have hyd :
      y ∈ (afterX.append q.reverse).support := by
    simpa [leftReturnDetour, afterX, p, q] using hydetour.1
  rw [SimpleGraph.Walk.mem_support_append_iff] at hyd
  rcases hyd with hyafter | hyq
  · exact hsplit.ne_of_mem_support_of_append
      hybefore.2.1 hybefore' hyafter rfl
  · have hyp : y ∈ p.support :=
      p.support_takeUntil_subset_support hx.1 hybefore'
    have hyq' : y ∈ q.support := by
      simpa [q, SimpleGraph.Walk.support_reverse] using hyq
    have hyright : y ≠ T.right := by
      intro hyr
      subst y
      exact (SimpleGraph.Walk.endpoint_notMem_support_takeUntil
        (T.route_isPath i) hx.1 hx.2.2.symm) hybefore'
    exact Set.disjoint_left.mp (T.interiors_disjoint i j hij)
      ⟨hyp, hybefore.2.2, hyright⟩
      ⟨hyq', hybefore.2.2, hyright⟩

/--
Public constructor for the left-return ear case.  The three routes are the
ear, the reversed prefix of arm `i`, and `leftReturnDetour`.
-/
noncomputable def leftReturnRotatedTheta
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G) {i j : Fin 3} (hij : i ≠ j)
    {x : V} (hx : x ∈ walkInterior (T.route i))
    (ear : G.Walk x T.left) (hear : ear.IsPath)
    (hsndEarPrefix :
      ear.snd ≠ ((T.route i).takeUntil x hx.1).reverse.snd)
    (hsndEarDetour :
      ear.snd ≠ (leftReturnDetour T i j hx.1).snd)
    (hsndPrefixDetour :
      ((T.route i).takeUntil x hx.1).reverse.snd ≠
        (leftReturnDetour T i j hx.1).snd)
    (hEarPrefix :
      Disjoint (walkInterior ear)
        (walkInterior ((T.route i).takeUntil x hx.1).reverse))
    (hEarDetour :
      Disjoint (walkInterior ear)
        (walkInterior (leftReturnDetour T i j hx.1)))
    : ThetaModel G :=
  thetaModelOfThreePaths hx.2.1
    ear
    ((T.route i).takeUntil x hx.1).reverse
    (leftReturnDetour T i j hx.1)
    hear
    ((T.route_isPath i).takeUntil hx.1).reverse
    (leftReturnDetour_isPath T hij hx)
    hsndEarPrefix hsndEarDetour hsndPrefixDetour
    hEarPrefix hEarDetour (leftReturnPrefix_disjoint_detour T hij hx)

/-- A left-return off-theta ear contradicts rank maximality as soon as the
rotated theta is known to cover the old theta and one new ear vertex. -/
theorem false_of_leftReturnRotatedTheta_new_vertex
    {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G)
    (hmax : ∀ T' : ThetaModel G, T'.rank ≤ T.rank)
    {i j : Fin 3} (hij : i ≠ j)
    {x : V} (hx : x ∈ walkInterior (T.route i))
    (ear : G.Walk x T.left) (hear : ear.IsPath)
    (hsndEarPrefix :
      ear.snd ≠ ((T.route i).takeUntil x hx.1).reverse.snd)
    (hsndEarDetour :
      ear.snd ≠ (leftReturnDetour T i j hx.1).snd)
    (hsndPrefixDetour :
      ((T.route i).takeUntil x hx.1).reverse.snd ≠
        (leftReturnDetour T i j hx.1).snd)
    (hEarPrefix :
      Disjoint (walkInterior ear)
        (walkInterior ((T.route i).takeUntil x hx.1).reverse))
    (hEarDetour :
      Disjoint (walkInterior ear)
        (walkInterior (leftReturnDetour T i j hx.1)))
    (hsub :
      T.vertexSet ⊆
        (leftReturnRotatedTheta T hij hx ear hear
          hsndEarPrefix hsndEarDetour hsndPrefixDetour
          hEarPrefix hEarDetour).vertexSet)
    {y : V} (hynew : y ∉ T.vertexSet)
    (hymem :
      y ∈ (leftReturnRotatedTheta T hij hx ear hear
        hsndEarPrefix hsndEarDetour hsndPrefixDetour
        hEarPrefix hEarDetour).vertexSet) :
    False := by
  let T' :=
    leftReturnRotatedTheta T hij hx ear hear
      hsndEarPrefix hsndEarDetour hsndPrefixDetour
      hEarPrefix hEarDetour
  exact T.not_vertexSet_subset_of_rank_maximal
    hmax T' hsub hynew hymem

end Lax16ThetaDirect
end Lax16Proofs
