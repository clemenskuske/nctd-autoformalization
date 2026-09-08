import Lax60Proofs.OuterplanarThetaDirect

namespace Lax60Proofs
namespace Lax60ThetaSameArmUse

open Lax60.PlanarGraphs
open Lax60ThetaDirect

universe u

set_option maxHeartbeats 2000000

/-- Every noninitial vertex of a path occurs after its second vertex. -/
lemma mem_dropUntil_snd_of_mem_support
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {a b z : V} (p : G.Walk a b)
    (hp : p.IsPath)
    (hsnd : p.snd ∈ walkInterior p)
    (hz : z ∈ p.support) (hza : z ≠ a) :
    z ∈ (p.dropUntil p.snd hsnd.1).support := by
  cases p with
  | nil =>
      exact (hsnd.2.1 rfl).elim
  | @cons a c b hac q =>
      have hzq : z ∈ q.support := by
        simpa only [SimpleGraph.Walk.support_cons, List.mem_cons,
          hza, false_or] using hz
      cases q with
      | nil =>
          simpa [SimpleGraph.Walk.dropUntil, hac.ne] using hzq
      | @cons c e b h r =>
          simp only [SimpleGraph.Walk.snd_cons,
            SimpleGraph.Walk.dropUntil, dif_neg hac.ne]
          exact hzq

/-- A one-edge walk has no support away from its endpoints. -/
lemma eq_start_or_eq_end_of_mem_support_of_length_one
    {V : Type u} {G : SimpleGraph V}
    {a b z : V} (p : G.Walk a b)
    (hlen : p.length = 1) (hz : z ∈ p.support) :
    z = a ∨ z = b := by
  cases p with
  | nil => simp at hlen
  | @cons a c b hac q =>
      cases q with
      | nil =>
          simpa using hz
      | cons h r =>
          simp at hlen

private lemma snd_dropUntil_snd_eq_getVert_two
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {a b : V} (p : G.Walk a b)
    (hsnd : p.snd ∈ p.support) :
    (p.dropUntil p.snd hsnd).snd = p.getVert 2 := by
  cases p with
  | nil => rfl
  | @cons a c b hac q =>
      cases q with
      | nil =>
          simp [SimpleGraph.Walk.dropUntil, hac.ne]
      | @cons c e b h r =>
          simp [SimpleGraph.Walk.dropUntil, hac.ne]
          exact SimpleGraph.Walk.snd_cons r h

private lemma length_takeUntil_snd_eq_one
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {a b : V} (p : G.Walk a b)
    (hsnd : p.snd ∈ p.support)
    (hsnd_ne : p.snd ≠ a) :
    (p.takeUntil p.snd hsnd).length = 1 := by
  cases p with
  | nil => exact (hsnd_ne rfl).elim
  | @cons a c b hac q =>
      simp [SimpleGraph.Walk.snd_cons,
        SimpleGraph.Walk.takeUntil, hac.ne]

private lemma snd_mem_interior_of_exists_interior
    {V : Type u} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (h : ∃ y, y ∈ walkInterior p) :
    p.snd ∈ walkInterior p := by
  have htwo : 2 ≤ p.length := by
    by_contra hn
    have hle : p.length ≤ 1 := by omega
    obtain ⟨y, hy⟩ := h
    rcases hy with ⟨hys, hya, hyb⟩
    cases p with
    | nil => simp_all [walkInterior]
    | @cons a c b hac q =>
        cases q with
        | nil => simp_all [walkInterior]
        | cons h r =>
            simp at hle
  refine ⟨p.getVert_mem_support 1, ?_, ?_⟩
  · intro heq
    have : (1 : ℕ) = 0 :=
      (hp.getVert_eq_start_iff (i := 1) (by omega)).mp heq
    omega
  · intro heq
    have : (1 : ℕ) = p.length :=
      (hp.getVert_eq_end_iff (i := 1) (by omega)).mp heq
    omega

private lemma two_le_length_of_snd_mem_interior
    {V : Type u} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b)
    (h : p.snd ∈ walkInterior p) :
    2 ≤ p.length := by
  by_contra hn
  have hle : p.length ≤ 1 := by omega
  cases p with
  | nil => exact h.2.1 rfl
  | @cons a c b hac q =>
      cases q with
      | nil => exact h.2.2 rfl
      | cons hq r => simp at hle

private lemma snd_eq_end_or_mem_interior
    {V : Type u} {G : SimpleGraph V}
    {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (hab : a ≠ b) :
    p.snd = b ∨ p.snd ∈ walkInterior p := by
  by_cases hone : p.length = 1
  · left
    simpa [hone] using p.getVert_length
  · right
    have hpositive : 0 < p.length := by
      by_contra hzero
      have : p.length = 0 := by omega
      exact hab (p.eq_of_length_eq_zero this)
    have htwo : 2 ≤ p.length := by omega
    refine ⟨p.getVert_mem_support 1, ?_, ?_⟩
    · intro heq
      have : (1 : ℕ) = 0 :=
        (hp.getVert_eq_start_iff (i := 1) (by omega)).mp heq
      omega
    · intro heq
      have : (1 : ℕ) = p.length :=
        (hp.getVert_eq_end_iff (i := 1) (by omega)).mp heq
      omega

private lemma support_subset_of_interior_subset
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

private lemma walkInterior_copy
    {V : Type u} {G : SimpleGraph V}
    {a b a' b' : V} (p : G.Walk a b)
    (ha : a = a') (hb : b = b') :
    walkInterior (p.copy ha hb) = walkInterior p := by
  subst a'
  subst b'
  rfl

/--
Specialized same-arm rotation.  The omitted third old arm is direct, so
the rotated theta covers the whole old theta.  Ordering `i` below `j`
makes the complementary detour strictly longer than the old span.
-/
lemma false_of_rank_maximal_same_arm_ear
    {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableEq V]
    (T : ThetaModel G)
    (hmax : ∀ T' : ThetaModel G, T'.rank ≤ T.rank)
    {i j d : Fin 3}
    (hij : i ≠ j) (hdi : d ≠ i) (hdj : d ≠ j)
    (hdir : (T.route d).length = 1)
    (E : ThetaEar T)
    (hstart : E.start = (T.route i).snd)
    (hx : (T.route i).snd ∈ walkInterior (T.route i))
    (hzarm : E.stop ∈ (T.route i).support)
    (hzleft : E.stop ≠ T.left)
    (horder : (T.route i).length ≤ (T.route j).length)
    (hstopOrNew :
      E.stop ≠ (T.route i).getVert 2 ∨
        ∃ y : V, y ∈ walkInterior E.route ∧ y ∉ T.vertexSet) :
    False := by
  classical
  have hzAfter : E.stop ∈
      ((T.route i).dropUntil (T.route i).snd hx.1).support :=
    mem_dropUntil_snd_of_mem_support (T.route i)
      (T.route_isPath i) hx hzarm hzleft
  have hxz : (T.route i).snd ≠ E.stop := by
    intro h
    apply E.endpoints_ne
    rw [hstart, h]
  let ear : G.Walk (T.route i).snd E.stop :=
    E.route.copy hstart rfl
  have hear : ear.IsPath := by
    simpa [ear] using E.route_isPath
  have hearAvoids :
      Disjoint (walkInterior ear) T.vertexSet := by
    simpa only [ear, walkInterior_copy] using E.interior_avoids
  have hearSnd :
      ear.snd = E.stop ∨ ear.snd ∈ walkInterior ear :=
    snd_eq_end_or_mem_interior ear hear hxz
  have hiTwo : 2 ≤ (T.route i).length :=
    two_le_length_of_snd_mem_interior (T.route i) hx
  have hsegSnd :
      (sameArmSegment T i hx.1 hzAfter).snd =
        (T.route i).getVert 2 := by
    unfold sameArmSegment
    rw [SimpleGraph.Walk.snd_takeUntil hxz.symm]
    exact snd_dropUntil_snd_eq_getVert_two (T.route i) hx.1
  have hbeforeLen :
      ((T.route i).takeUntil (T.route i).snd hx.1).length = 1 :=
    length_takeUntil_snd_eq_one (T.route i) hx.1 hx.2.1
  have hdetSnd :
      (sameArmDetour T i j hx.1 hzAfter).snd = T.left := by
    simp [sameArmDetour, SimpleGraph.Walk.snd,
      SimpleGraph.Walk.getVert_append, hbeforeLen]
    intro hjnil
    exact ((T.route j).eq_of_length_eq_zero
      hjnil.length_eq_zero).symm
  have hnextMem :
      (T.route i).getVert 2 ∈ T.vertexSet :=
    ⟨i, (T.route i).getVert_mem_support 2⟩
  have hsndEarSegment :
      ear.snd ≠ (sameArmSegment T i hx.1 hzAfter).snd := by
    rw [hsegSnd]
    rcases hstopOrNew with hstop | hnew
    · rcases hearSnd with hsndStop | hsndInt
      · intro heq
        exact hstop (hsndStop.symm.trans heq)
      · intro heq
        have hmem : ear.snd ∈ T.vertexSet := by
          rw [heq]
          exact hnextMem
        exact Set.disjoint_left.mp hearAvoids
          hsndInt hmem
    · have hsndInt : ear.snd ∈ walkInterior ear :=
        snd_mem_interior_of_exists_interior ear hear
          ⟨hnew.choose, by
            simpa only [ear, walkInterior_copy] using
              hnew.choose_spec.1⟩
      intro heq
      have hmem : ear.snd ∈ T.vertexSet := by
        rw [heq]
        exact hnextMem
      exact Set.disjoint_left.mp hearAvoids
        hsndInt hmem
  have hsndEarDetour :
      ear.snd ≠ (sameArmDetour T i j hx.1 hzAfter).snd := by
    rw [hdetSnd]
    rcases hearSnd with hsndStop | hsndInt
    · intro heq
      exact hzleft (hsndStop.symm.trans heq)
    · intro heq
      have hmem : ear.snd ∈ T.vertexSet := by
        rw [heq]
        exact T.left_mem_vertexSet
      exact Set.disjoint_left.mp hearAvoids
        hsndInt hmem
  have hsndSegmentDetour :
      (sameArmSegment T i hx.1 hzAfter).snd ≠
        (sameArmDetour T i j hx.1 hzAfter).snd := by
    rw [hsegSnd, hdetSnd]
    intro heq
    have : (2 : ℕ) = 0 :=
      ((T.route_isPath i).getVert_eq_start_iff
        (i := 2) (by omega)).mp heq
    omega
  have hEarSegment :
      Disjoint (walkInterior ear)
        (walkInterior (sameArmSegment T i hx.1 hzAfter)) :=
    hearAvoids.mono_right
      (sameArmSegment_interior_subset_vertexSet T i hx.1 hzAfter)
  have hEarDetour :
      Disjoint (walkInterior ear)
        (walkInterior (sameArmDetour T i j hx.1 hzAfter)) :=
    hearAvoids.mono_right
      (sameArmDetour_interior_subset_vertexSet T i j hx.1 hzAfter)
  have hSegmentDetour :
      Disjoint (walkInterior (sameArmSegment T i hx.1 hzAfter))
        (walkInterior (sameArmDetour T i j hx.1 hzAfter)) :=
    sameArmSegment_disjoint_detour T hij hx hzAfter hxz
  let T' : ThetaModel G :=
    sameArmRotatedTheta T hij hx hzAfter hxz ear hear
      hsndEarSegment hsndEarDetour hsndSegmentDetour
      hEarSegment hEarDetour hSegmentDetour
  let beforeX :=
    (T.route i).takeUntil (T.route i).snd hx.1
  let afterX :=
    (T.route i).dropUntil (T.route i).snd hx.1
  let middle := afterX.takeUntil E.stop hzAfter
  let afterZ := afterX.dropUntil E.stop hzAfter
  have hbeforeDetour :
      ∀ {y}, y ∈ beforeX.support →
        y ∈ (sameArmDetour T i j hx.1 hzAfter).support := by
    intro y hy
    simp only [sameArmDetour,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse]
    exact Or.inl (Or.inl (by simpa [beforeX] using hy))
  have hjDetour :
      ∀ {y}, y ∈ (T.route j).support →
        y ∈ (sameArmDetour T i j hx.1 hzAfter).support := by
    intro y hy
    simp only [sameArmDetour,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse]
    exact Or.inl (Or.inr hy)
  have hafterZDetour :
      ∀ {y}, y ∈ afterZ.support →
        y ∈ (sameArmDetour T i j hx.1 hzAfter).support := by
    intro y hy
    simp only [sameArmDetour,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse]
    exact Or.inr (by simpa [afterZ, afterX] using hy)
  have hindex (r : Fin 3) : r = i ∨ r = j ∨ r = d := by
    by_contra h
    push Not at h
    omega
  have hsub : T.vertexSet ⊆ T'.vertexSet := by
    intro y hy
    obtain ⟨r, hyr⟩ := hy
    rcases hindex r with hri | hrj | hrd
    · subst r
      have hySplit : y ∈ beforeX.support ∨ y ∈ afterX.support := by
        rw [← SimpleGraph.Walk.mem_support_append_iff]
        simpa [beforeX, afterX] using hyr
      rcases hySplit with hyBefore | hyAfter
      · refine ⟨2, ?_⟩
        change y ∈ (T'.route 2).support
        simpa [T', sameArmRotatedTheta] using
          hbeforeDetour hyBefore
      · have hySplitZ :
            y ∈ middle.support ∨ y ∈ afterZ.support := by
          rw [← SimpleGraph.Walk.mem_support_append_iff]
          simpa [middle, afterZ, afterX] using hyAfter
        rcases hySplitZ with hyMiddle | hyAfterZ
        · refine ⟨1, ?_⟩
          change y ∈ (T'.route 1).support
          simpa [T', sameArmRotatedTheta, sameArmSegment,
            middle, afterX] using hyMiddle
        · refine ⟨2, ?_⟩
          change y ∈ (T'.route 2).support
          simpa [T', sameArmRotatedTheta] using
            hafterZDetour hyAfterZ
    · subst r
      refine ⟨2, ?_⟩
      change y ∈ (T'.route 2).support
      simpa [T', sameArmRotatedTheta] using hjDetour hyr
    · subst r
      rcases eq_start_or_eq_end_of_mem_support_of_length_one
          (T.route d) hdir hyr with rfl | rfl
      · refine ⟨2, ?_⟩
        change T.left ∈ (T'.route 2).support
        simpa [T', sameArmRotatedTheta] using
          hjDetour (T.route j).start_mem_support
      · refine ⟨2, ?_⟩
        change T.right ∈ (T'.route 2).support
        simpa [T', sameArmRotatedTheta] using
          hjDetour (T.route j).end_mem_support
  have hjPositive : 1 ≤ (T.route j).length := by omega
  have hrouteLe (r : Fin 3) :
      (T.route r).length ≤ (T.route j).length := by
    rcases hindex r with rfl | rfl | rfl
    · exact horder
    · exact le_rfl
    · omega
  have hspanEq : T.span = (T.route j).length := by
    apply Nat.le_antisymm
    · simp only [ThetaModel.span, max_le_iff]
      exact ⟨hrouteLe 0, hrouteLe 1, hrouteLe 2⟩
    · exact T.route_length_le_span j
  have hdetLong :
      T.span < (sameArmDetour T i j hx.1 hzAfter).length := by
    rw [hspanEq]
    simp only [sameArmDetour, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse]
    rw [hbeforeLen]
    omega
  by_cases hnew :
      ∃ y : V, y ∈ walkInterior ear ∧ y ∉ T.vertexSet
  · obtain ⟨y, hyEar, hyNew⟩ := hnew
    have hyT' : y ∈ T'.vertexSet := by
      refine ⟨0, ?_⟩
      change y ∈ (T'.route 0).support
      simpa [T', sameArmRotatedTheta] using hyEar.1
    exact T.not_vertexSet_subset_of_rank_maximal
      hmax T' hsub hyNew hyT'
  · have hEarInteriorSub :
        walkInterior ear ⊆ T.vertexSet := by
      intro y hy
      by_contra hyout
      exact hnew ⟨y, hy, hyout⟩
    have hsegSupport :
        {y | y ∈ (sameArmSegment T i hx.1 hzAfter).support} ⊆
          T.vertexSet :=
      support_subset_of_interior_subset
        (sameArmSegment T i hx.1 hzAfter) T.vertexSet
        (T.route_support_subset_vertexSet i hx.1)
        ⟨i, hzarm⟩
        (sameArmSegment_interior_subset_vertexSet T i hx.1 hzAfter)
    have hdetSupport :
        {y | y ∈ (sameArmDetour T i j hx.1 hzAfter).support} ⊆
          T.vertexSet :=
      support_subset_of_interior_subset
        (sameArmDetour T i j hx.1 hzAfter) T.vertexSet
        (T.route_support_subset_vertexSet i hx.1)
        ⟨i, hzarm⟩
        (sameArmDetour_interior_subset_vertexSet T i j hx.1 hzAfter)
    have hearSupport :
        {y | y ∈ ear.support} ⊆ T.vertexSet :=
      support_subset_of_interior_subset ear T.vertexSet
        (T.route_support_subset_vertexSet i hx.1)
        E.stop_mem hEarInteriorSub
    have hreverse : T'.vertexSet ⊆ T.vertexSet := by
      intro y hy
      obtain ⟨r, hyr⟩ := hy
      fin_cases r
      · apply hearSupport
        simpa [T', sameArmRotatedTheta] using hyr
      · apply hsegSupport
        simpa [T', sameArmRotatedTheta] using hyr
      · apply hdetSupport
        simpa [T', sameArmRotatedTheta] using hyr
    exact T.not_longer_route_of_rank_maximal
      hmax T' (Set.Subset.antisymm hsub hreverse) 2
      (by simpa [T', sameArmRotatedTheta] using hdetLong)

end Lax60ThetaSameArmUse
end Lax60Proofs
