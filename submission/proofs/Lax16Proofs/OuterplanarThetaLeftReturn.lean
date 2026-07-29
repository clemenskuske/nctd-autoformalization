import Lax16Proofs.OuterplanarThetaDirect

namespace Lax16Proofs
namespace Lax16ThetaLeftReturnUse

open Lax16.PlanarGraphs
open Lax16ThetaDirect

universe u

theorem snd_mem_walkInterior_of_two_le
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

theorem length_takeUntil_snd_eq_one
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {a b : V} (p : G.Walk a b)
    (hsnd : p.snd ∈ p.support) (hsnd_ne : p.snd ≠ a) :
    (p.takeUntil p.snd hsnd).length = 1 := by
  cases p with
  | nil => exact (hsnd_ne rfl).elim
  | @cons a c b hac q =>
      simp [SimpleGraph.Walk.snd_cons,
        SimpleGraph.Walk.takeUntil, hac.ne]

theorem eq_start_or_eq_end_of_mem_support_of_length_one
    {V : Type u} {G : SimpleGraph V}
    {a b z : V} (p : G.Walk a b)
    (hlen : p.length = 1) (hz : z ∈ p.support) :
    z = a ∨ z = b := by
  cases p with
  | nil => simp at hlen
  | @cons a c b hac q =>
      cases q with
      | nil => simpa using hz
      | cons h r => simp at hlen

theorem support_subset_of_interior_subset
    {V : Type u} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (S : Set V)
    (ha : a ∈ S) (hb : b ∈ S)
    (hint : walkInterior p ⊆ S) :
    {y | y ∈ p.support} ⊆ S := by
  intro y hy
  by_cases hya : y = a
  · simpa [hya] using ha
  by_cases hyb : y = b
  · simpa [hyb] using hb
  exact hint ⟨hy, hya, hyb⟩

theorem walkInterior_copy
    {V : Type u} {G : SimpleGraph V}
    {a b a' b' : V} (p : G.Walk a b)
    (ha : a = a') (hb : b = b') :
    walkInterior (p.copy ha hb) = walkInterior p := by
  subst a'
  subst b'
  rfl

theorem two_le_length_of_exists_interior
    {V : Type u} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b)
    (h : ∃ y, y ∈ walkInterior p) :
    2 ≤ p.length := by
  by_contra hn
  have hle : p.length ≤ 1 := by omega
  obtain ⟨y, hy⟩ := h
  rcases hy with ⟨hys, hya, hyb⟩
  cases p with
  | nil => simp_all [walkInterior]
  | @cons a c b hac q =>
      cases q with
      | nil => simp_all [walkInterior]
      | cons h r => simp at hle

/-- One-shot handler for an off-theta first-return ear whose stop is the
old left endpoint.  The omitted old arm `d` is direct. -/
theorem false_of_rank_maximal_left_return_ear
    {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G)
    (hmax : ∀ T' : ThetaModel G, T'.rank ≤ T.rank)
    {i j d : Fin 3}
    (hij : i ≠ j) (hdi : d ≠ i) (hdj : d ≠ j)
    (hdir : (T.route d).length = 1)
    (E : ThetaEar T)
    (hstart : E.start = (T.route i).snd)
    (hx : (T.route i).snd ∈ walkInterior (T.route i))
    (hstop : E.stop = T.left)
    {y : V} (hyInterior : y ∈ walkInterior E.route)
    (hyOutside : y ∉ T.vertexSet) :
    False := by
  classical
  let x := (T.route i).snd
  let ear : G.Walk x T.left :=
    E.route.copy hstart hstop
  have hear : ear.IsPath := by
    simpa [ear] using E.route_isPath
  have hearAvoids :
      Disjoint (walkInterior ear) T.vertexSet := by
    simpa only [ear, walkInterior_copy] using E.interior_avoids
  have hyEar : y ∈ walkInterior ear := by
    simpa only [ear, walkInterior_copy] using hyInterior
  have hearTwo : 2 ≤ ear.length :=
    two_le_length_of_exists_interior ear ⟨y, hyEar⟩
  have hearSnd : ear.snd ∈ walkInterior ear :=
    snd_mem_walkInterior_of_two_le ear hear hearTwo
  have hbeforeLen :
      ((T.route i).takeUntil x hx.1).length = 1 :=
    length_takeUntil_snd_eq_one (T.route i) hx.1 hx.2.1
  have hprefixSnd :
      ((T.route i).takeUntil x hx.1).reverse.snd = T.left := by
    simp [SimpleGraph.Walk.snd, SimpleGraph.Walk.getVert_reverse,
      hbeforeLen]
  have hafterPositive :
      0 < ((T.route i).dropUntil x hx.1).length := by
    by_contra hzero
    have hz : ((T.route i).dropUntil x hx.1).length = 0 := by omega
    exact hx.2.2
      (((T.route i).dropUntil x hx.1).eq_of_length_eq_zero hz)
  have hjPositive : 0 < (T.route j).length := by
    by_contra hzero
    have hz : (T.route j).length = 0 := by omega
    exact T.endpoints_ne ((T.route j).eq_of_length_eq_zero hz)
  have hafterPositive' :
      0 < ((T.route i).dropUntil (T.route i).snd hx.1).length := by
    simpa [x] using hafterPositive
  have hdetTwo :
      2 ≤ (leftReturnDetour T i j hx.1).length := by
    simp only [leftReturnDetour, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse]
    omega
  have hdetPath :
      (leftReturnDetour T i j hx.1).IsPath :=
    leftReturnDetour_isPath T hij hx
  have hdetSnd :
      (leftReturnDetour T i j hx.1).snd ∈
        walkInterior (leftReturnDetour T i j hx.1) :=
    snd_mem_walkInterior_of_two_le _ hdetPath hdetTwo
  have hsndEarPrefix :
      ear.snd ≠ ((T.route i).takeUntil x hx.1).reverse.snd := by
    rw [hprefixSnd]
    intro heq
    exact Set.disjoint_left.mp hearAvoids hearSnd
      (by rw [heq]; exact T.left_mem_vertexSet)
  have hsndEarDetour :
      ear.snd ≠ (leftReturnDetour T i j hx.1).snd := by
    intro heq
    exact Set.disjoint_left.mp hearAvoids hearSnd
      (by
        rw [heq]
        exact leftReturnDetour_interior_subset_vertexSet
          T i j hx.1 hdetSnd)
  have hsndPrefixDetour :
      ((T.route i).takeUntil x hx.1).reverse.snd ≠
        (leftReturnDetour T i j hx.1).snd := by
    rw [hprefixSnd]
    exact hdetSnd.2.2.symm
  have hEarPrefix :
      Disjoint (walkInterior ear)
        (walkInterior ((T.route i).takeUntil x hx.1).reverse) :=
    hearAvoids.mono_right
      (leftReturnPrefix_interior_subset_vertexSet T i hx.1)
  have hEarDetour :
      Disjoint (walkInterior ear)
        (walkInterior (leftReturnDetour T i j hx.1)) :=
    hearAvoids.mono_right
      (leftReturnDetour_interior_subset_vertexSet T i j hx.1)
  let T' : ThetaModel G :=
    leftReturnRotatedTheta T hij hx ear hear
      hsndEarPrefix hsndEarDetour hsndPrefixDetour
      hEarPrefix hEarDetour
  let beforeX := (T.route i).takeUntil x hx.1
  let afterX := (T.route i).dropUntil x hx.1
  have hroute0 : T'.route 0 = ear := by rfl
  have hroute1 :
      T'.route 1 = ((T.route i).takeUntil x hx.1).reverse := by
    rfl
  have hroute2 :
      T'.route 2 = leftReturnDetour T i j hx.1 := by
    rfl
  have hindex (r : Fin 3) : r = i ∨ r = j ∨ r = d := by
    by_contra h
    push_neg at h
    omega
  have hsub : T.vertexSet ⊆ T'.vertexSet := by
    intro z hz
    obtain ⟨r, hzr⟩ := hz
    rcases hindex r with hri | hrj | hrd
    · subst r
      have hsplit : z ∈ beforeX.support ∨ z ∈ afterX.support := by
        rw [← SimpleGraph.Walk.mem_support_append_iff]
        simpa [beforeX, afterX, x] using hzr
      rcases hsplit with hbefore | hafter
      · refine ⟨1, ?_⟩
        rw [hroute1]
        change z ∈ beforeX.reverse.support
        rw [SimpleGraph.Walk.support_reverse]
        exact List.mem_reverse.mpr hbefore
      · refine ⟨2, ?_⟩
        rw [hroute2]
        unfold leftReturnDetour
        apply (SimpleGraph.Walk.mem_support_append_iff _ _).2
        exact Or.inl (by simpa [afterX, x] using hafter)
    · subst r
      refine ⟨2, ?_⟩
      rw [hroute2]
      unfold leftReturnDetour
      apply (SimpleGraph.Walk.mem_support_append_iff _ _).2
      refine Or.inr ?_
      have hm : z ∈ (T.route j).support.reverse :=
        List.mem_reverse.mpr hzr
      exact Eq.mpr
        (congrArg (fun l => z ∈ l)
          (SimpleGraph.Walk.support_reverse (T.route j))) hm
    · subst r
      rcases eq_start_or_eq_end_of_mem_support_of_length_one
        (T.route d) hdir hzr with rfl | rfl
      · refine ⟨1, ?_⟩
        rw [hroute1]
        exact ((T.route i).takeUntil x hx.1).reverse.end_mem_support
      · refine ⟨2, ?_⟩
        rw [hroute2]
        unfold leftReturnDetour
        apply (SimpleGraph.Walk.mem_support_append_iff _ _).2
        exact Or.inl
          ((T.route i).dropUntil (T.route i).snd hx.1).end_mem_support
  have hyT' : y ∈ T'.vertexSet := by
    refine ⟨0, ?_⟩
    rw [hroute0]
    exact hyEar.1
  exact T.not_vertexSet_subset_of_rank_maximal
    hmax T' hsub hyOutside hyT'

end Lax16ThetaLeftReturnUse
end Lax16Proofs
