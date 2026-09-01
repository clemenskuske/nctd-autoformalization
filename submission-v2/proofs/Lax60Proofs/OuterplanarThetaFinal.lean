import Lax60Proofs.OuterplanarThetaBase
import Lax60Proofs.OuterplanarThetaK4
import Lax60Proofs.OuterplanarThetaSameArm
import Lax60Proofs.OuterplanarThetaLeftReturn
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Fintype.Card

namespace Lax60Proofs
namespace Lax60ThetaFinal

open Lax60.PlanarGraphs
open Lax60ThetaDirect

universe u

set_option maxHeartbeats 2000000

private theorem walkInterior_cons_subset_tail
    {V : Type u} {G : SimpleGraph V}
    {a b c x : V} (h : G.Adj a b) (p : G.Walk b c)
    (hx : x ∈ walkInterior (.cons h p)) :
    x ∈ p.support := by
  rcases hx with ⟨hxsupport, hxne, _⟩
  simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hxsupport
  exact hxsupport.resolve_left hxne

private theorem snd_mem_walkInterior_of_two_le
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

/--
An edge leaving a theta extends, by two-connectedness, to a path whose
first return to the theta is its final vertex.
-/
theorem exists_firstReturnEar_of_adj_outside
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (htwo : IsTwoConnected G) (T : ThetaModel G)
    {x y : V}
    (hxmem : x ∈ T.vertexSet)
    (hxleft : x ≠ T.left)
    (hxy : G.Adj x y)
    (hyout : y ∉ T.vertexSet) :
    ∃ E : ThetaEar T,
      E.start = x ∧ y ∈ walkInterior E.route := by
  classical
  have hyx : y ≠ x := hxy.ne.symm
  have hleftx : T.left ≠ x := hxleft.symm
  obtain ⟨q, hq, hxq⟩ :=
    Lax60ThetaDirect.exists_path_avoiding_vertex G htwo hyx hleftx
  have hleftS : T.left ∈ T.vertexSet := T.left_mem_vertexSet
  obtain ⟨z, hzS, r, hr, hrfirst, hrsubq⟩ :=
    Lax60ThetaDirect.exists_initial_path_to_set
      T.vertexSet q hq hleftS
  have hxnotr : x ∉ r.support := by
    intro hxr
    exact hxq (hrsubq x hxr)
  have hxz : x ≠ z := by
    intro hxz
    apply hxnotr
    rw [hxz]
    exact r.end_mem_support
  let ear : G.Walk x z := .cons hxy r
  have hearPath : ear.IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff hxy r).mpr ⟨hr, hxnotr⟩
  have hyz : y ≠ z := by
    intro hyz
    apply hyout
    rw [hyz]
    exact hzS
  have hearLength : 2 ≤ ear.length := by
    simp only [ear, SimpleGraph.Walk.length_cons]
    have hrpositive : 0 < r.length := by
      by_contra hrzero
      have hzero : r.length = 0 := by omega
      exact hyz (r.eq_of_length_eq_zero hzero)
    omega
  have hyInterior : y ∈ walkInterior ear := by
    simpa [ear] using
      snd_mem_walkInterior_of_two_le ear hearPath hearLength
  refine ⟨
    { start := x
      stop := z
      endpoints_ne := hxz
      start_mem := hxmem
      stop_mem := hzS
      route := ear
      route_isPath := hearPath
      interior_avoids := ?_ },
    rfl, hyInterior⟩
  apply Set.disjoint_left.mpr
  intro w hwInterior hwT
  have hwr : w ∈ r.support :=
    walkInterior_cons_subset_tail hxy r hwInterior
  have hwz : w = z := hrfirst w hwr hwT
  exact hwInterior.2.2 hwz

/-- Besides two prescribed distinct vertices, degree at least three gives
another neighbor. -/
theorem exists_extra_neighbor
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    {v a b : V} (hab : a ≠ b) (hdegree : 3 ≤ G.degree v) :
    ∃ z : V, G.Adj v z ∧ z ≠ a ∧ z ≠ b := by
  classical
  by_contra hnone
  push Not at hnone
  have hsubset : G.neighborFinset v ⊆ {a, b} := by
    intro z hz
    have hvz : G.Adj v z := by simpa using hz
    by_cases hza : z = a
    · simp [hza]
    · have hzb : z = b := hnone z hvz hza
      simp [hzb]
  have hcard_le :
      (G.neighborFinset v).card ≤ ({a, b} : Finset V).card :=
    Finset.card_le_card hsubset
  have hpair : ({a, b} : Finset V).card = 2 := by
    simp [hab]
  rw [SimpleGraph.card_neighborFinset_eq_degree, hpair] at hcard_le
  omega

/-- At the second vertex of a long path, minimum degree three supplies an
edge other than the preceding and following path edges. -/
theorem exists_extra_neighbor_at_snd
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hlen : 2 ≤ p.length) (hdegree : 3 ≤ G.degree p.snd) :
    ∃ z : V,
      G.Adj p.snd z ∧ z ≠ a ∧ z ≠ p.getVert 2 := by
  have hdistinct : a ≠ p.getVert 2 := by
    intro h
    have hidx : (0 : ℕ) = 2 :=
      hp.getVert_injOn
        (by simp)
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simpa using h)
    omega
  exact exists_extra_neighbor G hdistinct hdegree

/--
The extra edge at the second vertex of a long theta arm either leaves the
theta, stays on that arm, or reaches a distinct arm.
-/
theorem extra_edge_trichotomy
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : ThetaModel G) [DecidableRel G.Adj]
    (hdegree : ∀ v : V, 3 ≤ G.degree v)
    {i : Fin 3} (hlen : 2 ≤ (T.route i).length) :
    ∃ z : V,
      G.Adj (T.route i).snd z ∧
      z ≠ T.left ∧
      z ≠ (T.route i).getVert 2 ∧
      (z ∉ T.vertexSet ∨
        z ∈ (T.route i).support ∨
        ∃ j : Fin 3, j ≠ i ∧ z ∈ (T.route j).support) := by
  obtain ⟨z, hzadj, hzleft, hznext⟩ :=
    exists_extra_neighbor_at_snd G (T.route i)
      (T.route_isPath i) hlen (hdegree (T.route i).snd)
  refine ⟨z, hzadj, hzleft, hznext, ?_⟩
  by_cases hzT : z ∈ T.vertexSet
  · obtain ⟨j, hzj⟩ := hzT
    by_cases hji : j = i
    · exact Or.inr (Or.inl (hji ▸ hzj))
    · exact Or.inr (Or.inr ⟨j, hji, hzj⟩)
  · exact Or.inl hzT

/--
Concrete extra-edge/ear case split.  The three handler arguments isolate the
remaining geometric verifications: same-arm rotation, first-return ear, and
cross-arm `K₄`.
-/
theorem rank_maximal_escape_of_cases
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj]
    (htwo : IsTwoConnected G)
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (T : ThetaModel G)
    {i : Fin 3} (hlen : 2 ≤ (T.route i).length)
    (hsame :
      ∀ (z : V),
        G.Adj (T.route i).snd z →
        z ≠ T.left →
        z ≠ (T.route i).getVert 2 →
        z ∈ (T.route i).support →
        False)
    (houtside :
      ∀ (z : V),
        G.Adj (T.route i).snd z →
        z ≠ T.left →
        z ≠ (T.route i).getVert 2 →
        z ∉ T.vertexSet →
        ∀ E : ThetaEar T,
          E.start = (T.route i).snd →
          z ∈ walkInterior E.route →
          False)
    (hcross :
      ∀ (z : V),
        G.Adj (T.route i).snd z →
        z ≠ T.left →
        z ≠ (T.route i).getVert 2 →
        ∀ (j : Fin 3),
          j ≠ i →
          z ∈ (T.route j).support →
          False) :
    False := by
  classical
  obtain ⟨z, hzadj, hzleft, hznext, hzcase⟩ :=
    extra_edge_trichotomy T hmin hlen
  rcases hzcase with hzout | hzsame | ⟨j, hji, hzj⟩
  · have hxint :
        (T.route i).snd ∈ walkInterior (T.route i) :=
      snd_mem_walkInterior_of_two_le
        (T.route i) (T.route_isPath i) hlen
    obtain ⟨E, hEstart, hzInterior⟩ :=
      exists_firstReturnEar_of_adj_outside htwo T
        (T.route_support_subset_vertexSet i hxint.1)
        hxint.2.1 hzadj hzout
    exact houtside z hzadj hzleft hznext hzout E hEstart hzInterior
  · exact hsame z hzadj hzleft hznext hzsame
  · exact hcross z hzadj hzleft hznext j hji hzj

private theorem eq_start_or_end_of_length_one
    {V : Type u} {G : SimpleGraph V} {a b z : V}
    (p : G.Walk a b) (hlen : p.length = 1)
    (hz : z ∈ p.support) :
    z = a ∨ z = b := by
  cases p with
  | nil => simp at hlen
  | @cons a c b hac q =>
      cases q with
      | nil =>
          simpa using hz
      | @cons c e b hce r =>
          simp at hlen

/--
The cross-arm branch is completely discharged by the compiled `K₄`
constructor.  A hit on the direct arm, or at the common right endpoint,
falls back to the same-arm handler.
-/
theorem rank_maximal_escape_of_same_and_outside
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj]
    (houter : IsOuterplanar G)
    (htwo : IsTwoConnected G)
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (T : ThetaModel G)
    (d i j : Fin 3)
    (hij : i ≠ j) (hdi : d ≠ i) (hdj : d ≠ j)
    (hd : (T.route d).length = 1)
    (hlen : 2 ≤ (T.route i).length)
    (hsame :
      ∀ (z : V),
        G.Adj (T.route i).snd z →
        z ≠ T.left →
        z ≠ (T.route i).getVert 2 →
        z ∈ (T.route i).support →
        False)
    (houtside :
      ∀ (z : V),
        G.Adj (T.route i).snd z →
        z ≠ T.left →
        z ≠ (T.route i).getVert 2 →
        z ∉ T.vertexSet →
        ∀ E : ThetaEar T,
          E.start = (T.route i).snd →
          z ∈ walkInterior E.route →
          False) :
    False := by
  classical
  apply rank_maximal_escape_of_cases htwo hmin T hlen hsame houtside
  intro z hzadj hzleft hznext k hki hzk
  have hk : k = d ∨ k = j := by
    fin_cases d <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp_all
  rcases hk with hkD | hkJ
  · have hklen : (T.route k).length = 1 := by
      simpa [hkD] using hd
    rcases eq_start_or_end_of_length_one
        (T.route k) hklen hzk with hzL | hzR
    · exact (hzleft hzL).elim
    · apply hsame z hzadj hzleft hznext
      rw [hzR]
      exact (T.route i).end_mem_support
  · by_cases hzright : z = T.right
    · apply hsame z hzadj hzleft hznext
      rw [hzright]
      exact (T.route i).end_mem_support
    · have hxint :
          (T.route i).snd ∈ walkInterior (T.route i) :=
        snd_mem_walkInterior_of_two_le
          (T.route i) (T.route_isPath i) hlen
      have hzint : z ∈ walkInterior (T.route k) :=
        ⟨hzk, hzleft, hzright⟩
      let E : ThetaEar T :=
        { start := (T.route i).snd
          stop := z
          endpoints_ne := hzadj.ne
          start_mem := T.route_support_subset_vertexSet i hxint.1
          stop_mem := T.route_support_subset_vertexSet k hzk
          route := SimpleGraph.Adj.toWalk hzadj
          route_isPath := SimpleGraph.Walk.IsPath.of_adj hzadj
          interior_avoids := by
            rw [Set.disjoint_left]
            intro w hw _
            simp only [walkInterior, SimpleGraph.Adj.toWalk,
              SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
              List.mem_cons, List.not_mem_nil, or_false] at hw
            rcases hw.1 with hwx | hwz
            · exact hw.2.1 hwx
            · exact hw.2.2 hwz }
      apply houter.1
      have hik : i ≠ k := Ne.symm hki
      have hdk : d ≠ k := by
        intro h
        apply hdj
        exact h.trans hkJ
      exact Lax60ThetaK4.hasTopologicalModel_k4_of_cross_arm_ear
        T i k d hik hdi hdk hd E hxint hzint

/--
Reduce the final escape argument to the three genuinely local theta
rotations: an on-arm chord, an off-theta ear returning to the same arm,
and an off-theta ear returning to the left endpoint.

Every other return is either the common right endpoint, hence a same-arm
return, or an internal point of the other long arm, hence a topological
`K₄`.
-/
theorem rank_maximal_escape_of_geometric_uses
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj]
    (houter : IsOuterplanar G)
    (htwo : IsTwoConnected G)
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (T : ThetaModel G)
    (d i j : Fin 3)
    (hij : i ≠ j) (hdi : d ≠ i) (hdj : d ≠ j)
    (hd : (T.route d).length = 1)
    (hlen : 2 ≤ (T.route i).length)
    (honArm :
      ∀ (z : V),
        G.Adj (T.route i).snd z →
        z ≠ T.left →
        z ≠ (T.route i).getVert 2 →
        z ∈ (T.route i).support →
        False)
    (hsameReturn :
      ∀ (z : V),
        G.Adj (T.route i).snd z →
        z ≠ T.left →
        z ≠ (T.route i).getVert 2 →
        z ∉ T.vertexSet →
        ∀ E : ThetaEar T,
          E.start = (T.route i).snd →
          z ∈ walkInterior E.route →
          E.stop ≠ T.left →
          E.stop ∈ (T.route i).support →
          False)
    (hleftReturn :
      ∀ (z : V),
        G.Adj (T.route i).snd z →
        z ≠ T.left →
        z ≠ (T.route i).getVert 2 →
        z ∉ T.vertexSet →
        ∀ E : ThetaEar T,
          E.start = (T.route i).snd →
          z ∈ walkInterior E.route →
          E.stop = T.left →
          False) :
    False := by
  classical
  apply rank_maximal_escape_of_same_and_outside
    houter htwo hmin T d i j hij hdi hdj hd hlen
  · intro z hzadj hzleft hznext hzsupport
    exact honArm z hzadj hzleft hznext hzsupport
  · intro z hzadj hzleft hznext hzout E hEstart hzInterior
    by_cases hstopLeft : E.stop = T.left
    · exact hleftReturn z hzadj hzleft hznext hzout E
        hEstart hzInterior hstopLeft
    have hEstartInterior :
        E.start ∈ walkInterior (T.route i) := by
      rw [hEstart]
      exact snd_mem_walkInterior_of_two_le
        (T.route i) (T.route_isPath i) hlen
    obtain ⟨k, hkSupport⟩ := E.stop_mem
    by_cases hki : k = i
    · apply hsameReturn z hzadj hzleft hznext hzout E
        hEstart hzInterior hstopLeft
      exact hki ▸ hkSupport
    have hk : k = d ∨ k = j := by
      by_contra h
      push_neg at h
      omega
    rcases hk with hkD | hkJ
    · have hkLength : (T.route k).length = 1 := by
        simpa [hkD] using hd
      rcases eq_start_or_end_of_length_one
          (T.route k) hkLength hkSupport with hstopL | hstopR
      · exact (hstopLeft hstopL).elim
      · apply hsameReturn z hzadj hzleft hznext hzout E
          hEstart hzInterior hstopLeft
        rw [hstopR]
        exact (T.route i).end_mem_support
    · by_cases hstopRight : E.stop = T.right
      · apply hsameReturn z hzadj hzleft hznext hzout E
          hEstart hzInterior hstopLeft
        rw [hstopRight]
        exact (T.route i).end_mem_support
      · have hstopInterior :
            E.stop ∈ walkInterior (T.route k) :=
          ⟨hkSupport, hstopLeft, hstopRight⟩
        apply houter.1
        have hik : i ≠ k := Ne.symm hki
        have hdk : d ≠ k := by
          intro h
          apply hdj
          exact h.trans hkJ
        exact Lax60ThetaK4.hasTopologicalModel_k4_of_cross_arm_ear
          T i k d hik hdi hdk hd E hEstartInterior hstopInterior

/--
The compiled same-arm replacement discharges both the chord and off-theta
same-arm return cases.  Only the left-return replacement remains as an
explicit callback.
-/
theorem rank_maximal_escape_of_left_return_use
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj]
    (houter : IsOuterplanar G)
    (htwo : IsTwoConnected G)
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (T : ThetaModel G)
    (hmax : ∀ T' : ThetaModel G, T'.rank ≤ T.rank)
    (d i j : Fin 3)
    (hij : i ≠ j) (hdi : d ≠ i) (hdj : d ≠ j)
    (hd : (T.route d).length = 1)
    (hlen : 2 ≤ (T.route i).length)
    (hle : (T.route i).length ≤ (T.route j).length)
    (hleftReturn :
      ∀ (z : V),
        G.Adj (T.route i).snd z →
        z ≠ T.left →
        z ≠ (T.route i).getVert 2 →
        z ∉ T.vertexSet →
        ∀ E : ThetaEar T,
          E.start = (T.route i).snd →
          z ∈ walkInterior E.route →
          E.stop = T.left →
          False) :
    False := by
  classical
  have hx :
      (T.route i).snd ∈ walkInterior (T.route i) :=
    snd_mem_walkInterior_of_two_le
      (T.route i) (T.route_isPath i) hlen
  apply rank_maximal_escape_of_geometric_uses
    houter htwo hmin T d i j hij hdi hdj hd hlen
  · intro z hzadj hzleft hznext hzSupport
    let E : ThetaEar T :=
      { start := (T.route i).snd
        stop := z
        endpoints_ne := hzadj.ne
        start_mem := T.route_support_subset_vertexSet i hx.1
        stop_mem := ⟨i, hzSupport⟩
        route := SimpleGraph.Adj.toWalk hzadj
        route_isPath := SimpleGraph.Walk.IsPath.of_adj hzadj
        interior_avoids := by
          rw [Set.disjoint_left]
          intro w hw _
          simp only [walkInterior, SimpleGraph.Adj.toWalk,
            SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
            List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw.1 with hwx | hwz
          · exact hw.2.1 hwx
          · exact hw.2.2 hwz }
    exact Lax60ThetaSameArmUse.false_of_rank_maximal_same_arm_ear
      T hmax hij hdi hdj hd E rfl hx
      hzSupport hzleft hle (Or.inl hznext)
  · intro z hzadj hzleft hznext hzout E hEstart hzInterior
      hstopLeft hstopSupport
    exact Lax60ThetaSameArmUse.false_of_rank_maximal_same_arm_ear
      T hmax hij hdi hdj hd E hEstart hx
      hstopSupport hstopLeft hle (Or.inr ⟨z, hzInterior, hzout⟩)
  · exact hleftReturn

/-- The complete rank-maximal-theta escape contradiction. -/
theorem rank_maximal_escape
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (houter : IsOuterplanar G)
    (htwo : IsTwoConnected G)
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (T : ThetaModel G)
    (hmax : ∀ T' : ThetaModel G, T'.rank ≤ T.rank)
    (d i j : Fin 3)
    (hd : (T.route d).length = 1)
    (hij : i ≠ j) (hid : i ≠ d) (hjd : j ≠ d)
    (hlen : 2 ≤ (T.route i).length)
    (hle : (T.route i).length ≤ (T.route j).length) :
    False := by
  classical
  have hx :
      (T.route i).snd ∈ walkInterior (T.route i) :=
    snd_mem_walkInterior_of_two_le
      (T.route i) (T.route_isPath i) hlen
  apply rank_maximal_escape_of_left_return_use
    houter htwo hmin T hmax d i j hij hid.symm hjd.symm
      hd hlen hle
  intro z hzadj hzleft hznext hzout E hEstart hzInterior hEstop
  exact Lax60ThetaLeftReturnUse.false_of_rank_maximal_left_return_ear
    T hmax hij hid.symm hjd.symm hd E hEstart hx hEstop
    hzInterior hzout

private theorem direct_arm_unique
    {V : Type u} {G : SimpleGraph V}
    (T : ThetaModel G) {i j : Fin 3}
    (hi : (T.route i).length = 1)
    (hj : (T.route j).length = 1) :
    i = j := by
  apply T.route_snd_injective
  change (T.route i).snd = (T.route j).snd
  have hisnd : (T.route i).snd = T.right := by
    simpa [SimpleGraph.Walk.snd, hi] using
      (T.route i).getVert_length
  have hjsnd : (T.route j).snd = T.right := by
    simpa [SimpleGraph.Walk.snd, hj] using
      (T.route j).getVert_length
  rw [hisnd, hjsnd]

/-- Order the two arms complementary to `d` by length. -/
private theorem exists_ordered_other_arms
    {V : Type u} {G : SimpleGraph V}
    (T : ThetaModel G) (d : Fin 3) :
    ∃ i j : Fin 3,
      i ≠ j ∧ i ≠ d ∧ j ≠ d ∧
      (T.route i).length ≤ (T.route j).length := by
  fin_cases d
  · by_cases h :
        (T.route (1 : Fin 3)).length ≤ (T.route (2 : Fin 3)).length
    · exact ⟨1, 2, by decide, by decide, by decide, h⟩
    · exact ⟨2, 1, by decide, by decide, by decide, Nat.le_of_not_ge h⟩
  · by_cases h :
        (T.route (0 : Fin 3)).length ≤ (T.route (2 : Fin 3)).length
    · exact ⟨0, 2, by decide, by decide, by decide, h⟩
    · exact ⟨2, 0, by decide, by decide, by decide, Nat.le_of_not_ge h⟩
  · by_cases h :
        (T.route (0 : Fin 3)).length ≤ (T.route (1 : Fin 3)).length
    · exact ⟨0, 1, by decide, by decide, by decide, h⟩
    · exact ⟨1, 0, by decide, by decide, by decide, Nat.le_of_not_ge h⟩

/--
Common setup for the final contradiction: choose a rank-maximal theta, its
unique direct arm, and the shorter of the two remaining arms.
-/
theorem min_degree_three_false_of_rank_maximal_escape
    (escape :
      ∀ {W : Type u} [Fintype W] (H : SimpleGraph W)
        [DecidableRel H.Adj],
        IsOuterplanar H →
        IsTwoConnected H →
        (∀ w : W, 3 ≤ H.degree w) →
        ∀ (T : ThetaModel H),
          (∀ T' : ThetaModel H, T'.rank ≤ T.rank) →
          ∀ (d i j : Fin 3),
            (T.route d).length = 1 →
            i ≠ j → i ≠ d → j ≠ d →
            2 ≤ (T.route i).length →
            (T.route i).length ≤ (T.route j).length →
            False)
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (houter : IsOuterplanar G)
    (htwo : IsTwoConnected G)
    (hmin : ∀ v : V, 3 ≤ G.degree v) :
    False := by
  classical
  have hnonempty : Nonempty V :=
    Fintype.card_pos_iff.mp (by
      have hthree := htwo.1
      rw [← Nat.card_eq_fintype_card]
      omega)
  letI : Nonempty V := hnonempty
  obtain ⟨T₀, -⟩ :=
    Lax60ThetaDirect.exists_theta_of_degree_three G htwo
      (Classical.choice hnonempty) (hmin _)
  obtain ⟨T, hmax⟩ := T₀.exists_rank_maximal
  obtain ⟨d, hd⟩ := T.exists_length_one_of_no_k23 houter.2
  obtain ⟨i, j, hij, hid, hjd, hle⟩ :=
    exists_ordered_other_arms T d
  have hlen : 2 ≤ (T.route i).length := by
    have hpos : 0 < (T.route i).length := by
      by_contra hzero
      have hz : (T.route i).length = 0 := by omega
      exact T.endpoints_ne ((T.route i).eq_of_length_eq_zero hz)
    have hneone : (T.route i).length ≠ 1 := by
      intro hi
      exact hid (direct_arm_unique T hi hd)
    omega
  exact escape G houter htwo hmin T hmax d i j hd hij hid hjd hlen hle

/-- Two-connectedness forces every vertex to have at least two neighbors. -/
theorem two_le_degree_of_twoConnected
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (htwo : IsTwoConnected G) (v : V) :
    2 ≤ G.degree v := by
  classical
  have hcard : 3 ≤ Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using htwo.1
  obtain ⟨y, hyv⟩ : ∃ y : V, y ≠ v := by
    have hnontrivial : Nontrivial V :=
      Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    letI : Nontrivial V := hnontrivial
    exact exists_ne v
  obtain ⟨t, htv, hty⟩ : ∃ t : V, t ≠ v ∧ t ≠ y := by
    by_contra! hall
    have huniv : (Finset.univ : Finset V) ⊆ {v, y} := by
      intro z hz
      by_cases hzv : z = v
      · simp [hzv]
      · have hzy : z = y := hall z hzv
        simp [hzy]
    have hle : Fintype.card V ≤ ({v, y} : Finset V).card := by
      simpa using Finset.card_le_card huniv
    have hpair : ({v, y} : Finset V).card = 2 := by
      simp [hyv.symm]
    omega
  let vY : {z : V // z ≠ y} := ⟨v, hyv.symm⟩
  let tY : {z : V // z ≠ y} := ⟨t, hty⟩
  have hvY_ne_tY : vY ≠ tY := by
    intro h
    exact htv (congrArg Subtype.val h).symm
  obtain ⟨p, hp⟩ :=
    (htwo.2 y).exists_isPath vY tY
  have hp_nonNil : ¬p.Nil := by
    intro hnil
    exact hvY_ne_tY hnil.eq
  have hvz_induced :
      (G.induce {z : V | z ≠ y}).Adj vY p.snd :=
    SimpleGraph.Walk.adj_snd hp_nonNil
  let z : V := p.snd.1
  have hvz : G.Adj v z := hvz_induced
  have hzy : z ≠ y := p.snd.2
  have hzv : z ≠ v := hvz.ne.symm
  let vZ : {w : V // w ≠ z} := ⟨v, hzv.symm⟩
  let yZ : {w : V // w ≠ z} := ⟨y, hzy.symm⟩
  have hvZ_ne_yZ : vZ ≠ yZ := by
    intro h
    exact hyv (congrArg Subtype.val h).symm
  obtain ⟨q, hq⟩ :=
    (htwo.2 z).exists_isPath vZ yZ
  have hq_nonNil : ¬q.Nil := by
    intro hnil
    exact hvZ_ne_yZ hnil.eq
  have hvw_induced :
      (G.induce {w : V | w ≠ z}).Adj vZ q.snd :=
    SimpleGraph.Walk.adj_snd hq_nonNil
  let w : V := q.snd.1
  have hvw : G.Adj v w := hvw_induced
  have hwz : w ≠ z := q.snd.2
  have hz_mem : z ∈ G.neighborFinset v := by simpa using hvz
  have hw_mem : w ∈ G.neighborFinset v := by simpa using hvw
  exact Finset.one_lt_card.mpr ⟨z, hz_mem, w, hw_mem, hwz.symm⟩

/--
Once minimum degree three has been contradicted, two-connectedness upgrades
the resulting degree bound to equality two.
-/
theorem exists_degree_two_of_min_degree_contradiction
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (htwo : IsTwoConnected G)
    (hcontra : (∀ v : V, 3 ≤ G.degree v) → False) :
    ∃ v : V, G.degree v = 2 := by
  classical
  by_contra hnone
  have hmin (v : V) : 3 ≤ G.degree v := by
    have htwoDegree := two_le_degree_of_twoConnected G htwo v
    have hne : G.degree v ≠ 2 := by
      intro heq
      exact hnone ⟨v, heq⟩
    omega
  exact hcontra hmin

/--
The final structural seam: it is enough to rule out minimum degree three
using the rank-maximal theta construction.
-/
theorem exists_degree_two_of_theta_contradiction
    (theta_contra :
      ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
        ∀ [DecidableRel H.Adj],
        IsOuterplanar H →
        IsTwoConnected H →
        (∀ w : W, 3 ≤ H.degree w) →
        False)
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (houter : IsOuterplanar G)
    (htwo : IsTwoConnected G) :
    ∃ v : V, G.degree v = 2 :=
  exists_degree_two_of_min_degree_contradiction G htwo
    (theta_contra G houter htwo)

/-- An outerplanar two-connected finite graph cannot have minimum degree
at least three. -/
theorem min_degree_three_false
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (houter : IsOuterplanar G)
    (htwo : IsTwoConnected G)
    (hmin : ∀ v : V, 3 ≤ G.degree v) :
    False :=
  min_degree_three_false_of_rank_maximal_escape
    rank_maximal_escape G houter htwo hmin

/-- Every finite outerplanar two-connected graph has a vertex of degree
exactly two. -/
theorem exists_degree_two_outerplanar_twoConnected
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (houter : IsOuterplanar G)
    (htwo : IsTwoConnected G) :
    ∃ v : V, G.degree v = 2 :=
  exists_degree_two_of_theta_contradiction
    (fun H _ hHouter hHtwo hmin =>
      min_degree_three_false H hHouter hHtwo hmin)
    G houter htwo

end Lax60ThetaFinal
end Lax60Proofs
