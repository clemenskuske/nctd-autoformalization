import Lax16Proofs.OuterplanarThetaDirect
import Mathlib.Tactic.FinCases

namespace Lax16Proofs
namespace Lax16ThetaK4

open Lax16.PlanarGraphs
open Lax16ThetaDirect

universe u

set_option maxHeartbeats 2000000

private lemma walkInterior_eq_empty_of_length_eq_one
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hlen : p.length = 1) :
    walkInterior p = ∅ := by
  cases p with
  | nil => simp at hlen
  | @cons a c b hac q =>
      cases q with
      | nil =>
          ext y
          simp only [walkInterior, SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil, List.mem_cons,
            Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          aesop
      | cons h r =>
          simp at hlen

/--
A theta with a direct third arm and a cross-arm ear contains a subdivision
of `K₄`.  The four branch vertices are the theta endpoints and the two ear
endpoints.  The six routes are the direct arm, the two halves of each crossed
arm, and the ear.
-/
lemma hasTopologicalModel_k4_of_cross_arm_ear
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (T : ThetaModel G)
    (i j k : Fin 3)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hdir : (T.route k).length = 1)
    (E : ThetaEar T)
    (hx : E.start ∈ walkInterior (T.route i))
    (hz : E.stop ∈ walkInterior (T.route j)) :
    HasTopologicalModel (⊤ : SimpleGraph (Fin 4)) G := by
  classical
  let pLX : G.Walk T.left E.start :=
    (T.route i).takeUntil E.start hx.1
  let pXR : G.Walk E.start T.right :=
    (T.route i).dropUntil E.start hx.1
  let pLZ : G.Walk T.left E.stop :=
    (T.route j).takeUntil E.stop hz.1
  let pZR : G.Walk E.stop T.right :=
    (T.route j).dropUntil E.stop hz.1
  let pLR : G.Walk T.left T.right := T.route k
  let pXZ : G.Walk E.start E.stop := E.route
  have hpLX : pLX.IsPath := (T.route_isPath i).takeUntil hx.1
  have hpXR : pXR.IsPath := (T.route_isPath i).dropUntil hx.1
  have hpLZ : pLZ.IsPath := (T.route_isPath j).takeUntil hz.1
  have hpZR : pZR.IsPath := (T.route_isPath j).dropUntil hz.1
  have hpLR : pLR.IsPath := T.route_isPath k
  have hpXZ : pXZ.IsPath := E.route_isPath
  have hLXsub :
      walkInterior pLX ⊆ walkInterior (T.route i) := by
    exact walkInterior_takeUntil_subset
      (T.route i) (T.route_isPath i) hx
  have hXRsub :
      walkInterior pXR ⊆ walkInterior (T.route i) := by
    exact walkInterior_dropUntil_subset
      (T.route i) (T.route_isPath i) hx
  have hLZsub :
      walkInterior pLZ ⊆ walkInterior (T.route j) := by
    exact walkInterior_takeUntil_subset
      (T.route j) (T.route_isPath j) hz
  have hZRsub :
      walkInterior pZR ⊆ walkInterior (T.route j) := by
    exact walkInterior_dropUntil_subset
      (T.route j) (T.route_isPath j) hz
  have hLXvertex : walkInterior pLX ⊆ T.vertexSet :=
    fun _ hy => ⟨i, (hLXsub hy).1⟩
  have hXRvertex : walkInterior pXR ⊆ T.vertexSet :=
    fun _ hy => ⟨i, (hXRsub hy).1⟩
  have hLZvertex : walkInterior pLZ ⊆ T.vertexSet :=
    fun _ hy => ⟨j, (hLZsub hy).1⟩
  have hZRvertex : walkInterior pZR ⊆ T.vertexSet :=
    fun _ hy => ⟨j, (hZRsub hy).1⟩
  have hLRempty : walkInterior pLR = ∅ := by
    exact walkInterior_eq_empty_of_length_eq_one pLR hdir
  have hLX_XR :
      Disjoint (walkInterior pLX) (walkInterior pXR) := by
    exact disjoint_walkInterior_takeUntil_dropUntil
      (T.route i) (T.route_isPath i) hx.1
  have hLZ_ZR :
      Disjoint (walkInterior pLZ) (walkInterior pZR) := by
    exact disjoint_walkInterior_takeUntil_dropUntil
      (T.route j) (T.route_isPath j) hz.1
  have hLX_LZ :
      Disjoint (walkInterior pLX) (walkInterior pLZ) :=
    (T.interiors_disjoint i j hij).mono hLXsub hLZsub
  have hLX_ZR :
      Disjoint (walkInterior pLX) (walkInterior pZR) :=
    (T.interiors_disjoint i j hij).mono hLXsub hZRsub
  have hXR_LZ :
      Disjoint (walkInterior pXR) (walkInterior pLZ) :=
    (T.interiors_disjoint i j hij).mono hXRsub hLZsub
  have hXR_ZR :
      Disjoint (walkInterior pXR) (walkInterior pZR) :=
    (T.interiors_disjoint i j hij).mono hXRsub hZRsub
  have hXZ_LX :
      Disjoint (walkInterior pXZ) (walkInterior pLX) :=
    E.interior_avoids.mono Set.Subset.rfl hLXvertex
  have hXZ_XR :
      Disjoint (walkInterior pXZ) (walkInterior pXR) :=
    E.interior_avoids.mono Set.Subset.rfl hXRvertex
  have hXZ_LZ :
      Disjoint (walkInterior pXZ) (walkInterior pLZ) :=
    E.interior_avoids.mono Set.Subset.rfl hLZvertex
  have hXZ_ZR :
      Disjoint (walkInterior pXZ) (walkInterior pZR) :=
    E.interior_avoids.mono Set.Subset.rfl hZRvertex
  let branchFun : Fin 4 → V :=
    ![T.left, T.right, E.start, E.stop]
  have hbranchFun : Function.Injective branchFun := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp [branchFun] at hab ⊢
    · exact (T.endpoints_ne hab).elim
    · exact (hx.2.1 hab.symm).elim
    · exact (hz.2.1 hab.symm).elim
    · exact (T.endpoints_ne hab.symm).elim
    · exact (hx.2.2 hab.symm).elim
    · exact (hz.2.2 hab.symm).elim
    · exact (hx.2.1 hab).elim
    · exact (hx.2.2 hab).elim
    · exact (E.endpoints_ne hab).elim
    · exact (hz.2.1 hab).elim
    · exact (hz.2.2 hab).elim
    · exact (E.endpoints_ne hab.symm).elim
  let branch : Fin 4 ↪ V := ⟨branchFun, hbranchFun⟩
  have hbranchVertex (w : Fin 4) : branch w ∈ T.vertexSet := by
    fin_cases w
    · simpa [branch, branchFun] using T.left_mem_vertexSet
    · simpa [branch, branchFun] using T.right_mem_vertexSet
    · exact ⟨i, hx.1⟩
    · exact ⟨j, hz.1⟩
  have havoidLR (w : Fin 4) :
      branch w ∉ walkInterior pLR := by
    rw [hLRempty]
    simp
  have havoidLX (w : Fin 4) :
      branch w ∉ walkInterior pLX := by
    intro hw
    fin_cases w
    · exact (hLXsub hw).2.1 (by simp [branch, branchFun])
    · exact (hLXsub hw).2.2 (by simp [branch, branchFun])
    · exact hw.2.2 (by simp [branch, branchFun, pLX])
    · exact Set.disjoint_left.mp (T.interiors_disjoint i j hij)
        (hLXsub hw) hz
  have havoidXR (w : Fin 4) :
      branch w ∉ walkInterior pXR := by
    intro hw
    fin_cases w
    · exact (hXRsub hw).2.1 (by simp [branch, branchFun])
    · exact (hXRsub hw).2.2 (by simp [branch, branchFun])
    · exact hw.2.1 (by simp [branch, branchFun, pXR])
    · exact Set.disjoint_left.mp (T.interiors_disjoint i j hij)
        (hXRsub hw) hz
  have havoidLZ (w : Fin 4) :
      branch w ∉ walkInterior pLZ := by
    intro hw
    fin_cases w
    · exact (hLZsub hw).2.1 (by simp [branch, branchFun])
    · exact (hLZsub hw).2.2 (by simp [branch, branchFun])
    · exact Set.disjoint_left.mp (T.interiors_disjoint j i (Ne.symm hij))
        (hLZsub hw) hx
    · exact hw.2.2 (by simp [branch, branchFun, pLZ])
  have havoidZR (w : Fin 4) :
      branch w ∉ walkInterior pZR := by
    intro hw
    fin_cases w
    · exact (hZRsub hw).2.1 (by simp [branch, branchFun])
    · exact (hZRsub hw).2.2 (by simp [branch, branchFun])
    · exact Set.disjoint_left.mp (T.interiors_disjoint j i (Ne.symm hij))
        (hZRsub hw) hx
    · exact hw.2.1 (by simp [branch, branchFun, pZR])
  have havoidXZ (w : Fin 4) :
      branch w ∉ walkInterior pXZ := by
    intro hw
    exact Set.disjoint_left.mp E.interior_avoids hw (hbranchVertex w)
  let route : ∀ {a b : Fin 4}, (⊤ : SimpleGraph (Fin 4)).Adj a b →
      G.Walk (branch a) (branch b) := by
    intro a b hab
    by_cases ha0 : a = 0
    · subst a
      by_cases hb0 : b = 0
      · subst b
        exact (hab rfl).elim
      by_cases hb1 : b = 1
      · subst b
        simpa [branch, branchFun] using pLR
      by_cases hb2 : b = 2
      · subst b
        simpa [branch, branchFun] using pLX
      have hb3 : b = 3 := by omega
      subst b
      simpa [branch, branchFun] using pLZ
    by_cases ha1 : a = 1
    · subst a
      by_cases hb0 : b = 0
      · subst b
        simpa [branch, branchFun] using pLR.reverse
      by_cases hb1 : b = 1
      · subst b
        exact (hab rfl).elim
      by_cases hb2 : b = 2
      · subst b
        simpa [branch, branchFun] using pXR.reverse
      have hb3 : b = 3 := by omega
      subst b
      simpa [branch, branchFun] using pZR.reverse
    by_cases ha2 : a = 2
    · subst a
      by_cases hb0 : b = 0
      · subst b
        simpa [branch, branchFun] using pLX.reverse
      by_cases hb1 : b = 1
      · subst b
        simpa [branch, branchFun] using pXR
      by_cases hb2 : b = 2
      · subst b
        exact (hab rfl).elim
      have hb3 : b = 3 := by omega
      subst b
      simpa [branch, branchFun] using pXZ
    have ha3 : a = 3 := by omega
    subst a
    by_cases hb0 : b = 0
    · subst b
      simpa [branch, branchFun] using pLZ.reverse
    by_cases hb1 : b = 1
    · subst b
      simpa [branch, branchFun] using pZR
    by_cases hb2 : b = 2
    · subst b
      simpa [branch, branchFun] using pXZ.reverse
    have hb3 : b = 3 := by omega
    subst b
    exact (hab rfl).elim
  have hroutePath {a b : Fin 4}
      (hab : (⊤ : SimpleGraph (Fin 4)).Adj a b) :
      (route hab).IsPath := by
    by_cases ha0 : a = 0
    · subst a
      by_cases hb0 : b = 0
      · subst b
        exact (hab rfl).elim
      by_cases hb1 : b = 1
      · subst b
        simpa [route] using hpLR
      by_cases hb2 : b = 2
      · subst b
        simpa [route] using hpLX
      have hb3 : b = 3 := by omega
      subst b
      simpa [route] using hpLZ
    by_cases ha1 : a = 1
    · subst a
      by_cases hb0 : b = 0
      · subst b
        change pLR.reverse.IsPath
        exact hpLR.reverse
      by_cases hb1 : b = 1
      · subst b
        exact (hab rfl).elim
      by_cases hb2 : b = 2
      · subst b
        change pXR.reverse.IsPath
        exact hpXR.reverse
      have hb3 : b = 3 := by omega
      subst b
      change pZR.reverse.IsPath
      exact hpZR.reverse
    by_cases ha2 : a = 2
    · subst a
      by_cases hb0 : b = 0
      · subst b
        change pLX.reverse.IsPath
        exact hpLX.reverse
      by_cases hb1 : b = 1
      · subst b
        simpa [route] using hpXR
      by_cases hb2 : b = 2
      · subst b
        exact (hab rfl).elim
      have hb3 : b = 3 := by omega
      subst b
      simpa [route] using hpXZ
    have ha3 : a = 3 := by omega
    subst a
    by_cases hb0 : b = 0
    · subst b
      change pLZ.reverse.IsPath
      exact hpLZ.reverse
    by_cases hb1 : b = 1
    · subst b
      simpa [route] using hpZR
    by_cases hb2 : b = 2
    · subst b
      change pXZ.reverse.IsPath
      exact hpXZ.reverse
    have hb3 : b = 3 := by omega
    subst b
    exact (hab rfl).elim
  have hrouteAvoids {a b : Fin 4}
      (hab : (⊤ : SimpleGraph (Fin 4)).Adj a b) (w : Fin 4) :
      branch w ∉ walkInterior (route hab) := by
    by_cases ha0 : a = 0
    · subst a
      by_cases hb0 : b = 0
      · subst b
        exact (hab rfl).elim
      by_cases hb1 : b = 1
      · subst b
        simpa [route] using havoidLR w
      by_cases hb2 : b = 2
      · subst b
        simpa [route] using havoidLX w
      have hb3 : b = 3 := by omega
      subst b
      simpa [route] using havoidLZ w
    by_cases ha1 : a = 1
    · subst a
      by_cases hb0 : b = 0
      · subst b
        change branch w ∉ walkInterior pLR.reverse
        rw [walkInterior_reverse]
        exact havoidLR w
      by_cases hb1 : b = 1
      · subst b
        exact (hab rfl).elim
      by_cases hb2 : b = 2
      · subst b
        change branch w ∉ walkInterior pXR.reverse
        rw [walkInterior_reverse]
        exact havoidXR w
      have hb3 : b = 3 := by omega
      subst b
      change branch w ∉ walkInterior pZR.reverse
      rw [walkInterior_reverse]
      exact havoidZR w
    by_cases ha2 : a = 2
    · subst a
      by_cases hb0 : b = 0
      · subst b
        change branch w ∉ walkInterior pLX.reverse
        rw [walkInterior_reverse]
        exact havoidLX w
      by_cases hb1 : b = 1
      · subst b
        simpa [route] using havoidXR w
      by_cases hb2 : b = 2
      · subst b
        exact (hab rfl).elim
      have hb3 : b = 3 := by omega
      subst b
      simpa [route] using havoidXZ w
    have ha3 : a = 3 := by omega
    subst a
    by_cases hb0 : b = 0
    · subst b
      change branch w ∉ walkInterior pLZ.reverse
      rw [walkInterior_reverse]
      exact havoidLZ w
    by_cases hb1 : b = 1
    · subst b
      simpa [route] using havoidZR w
    by_cases hb2 : b = 2
    · subst b
      change branch w ∉ walkInterior pXZ.reverse
      rw [walkInterior_reverse]
      exact havoidXZ w
    have hb3 : b = 3 := by omega
    subst b
    exact (hab rfl).elim
  let edgeInterior (e : Sym2 (Fin 4)) : Set V :=
    if e = s(0, 1) then walkInterior pLR
    else if e = s(0, 2) then walkInterior pLX
    else if e = s(1, 2) then walkInterior pXR
    else if e = s(0, 3) then walkInterior pLZ
    else if e = s(1, 3) then walkInterior pZR
    else if e = s(2, 3) then walkInterior pXZ
    else ∅
  have hrouteInterior {a b : Fin 4}
      (hab : (⊤ : SimpleGraph (Fin 4)).Adj a b) :
      walkInterior (route hab) = edgeInterior s(a, b) := by
    by_cases ha0 : a = 0
    · subst a
      by_cases hb0 : b = 0
      · subst b
        exact (hab rfl).elim
      by_cases hb1 : b = 1
      · subst b
        change walkInterior pLR = walkInterior pLR
        rfl
      by_cases hb2 : b = 2
      · subst b
        change walkInterior pLX = walkInterior pLX
        rfl
      have hb3 : b = 3 := by omega
      subst b
      change walkInterior pLZ = walkInterior pLZ
      rfl
    by_cases ha1 : a = 1
    · subst a
      by_cases hb0 : b = 0
      · subst b
        change walkInterior pLR.reverse = walkInterior pLR
        exact walkInterior_reverse pLR
      by_cases hb1 : b = 1
      · subst b
        exact (hab rfl).elim
      by_cases hb2 : b = 2
      · subst b
        change walkInterior pXR.reverse = walkInterior pXR
        exact walkInterior_reverse pXR
      have hb3 : b = 3 := by omega
      subst b
      change walkInterior pZR.reverse = walkInterior pZR
      exact walkInterior_reverse pZR
    by_cases ha2 : a = 2
    · subst a
      by_cases hb0 : b = 0
      · subst b
        change walkInterior pLX.reverse = walkInterior pLX
        exact walkInterior_reverse pLX
      by_cases hb1 : b = 1
      · subst b
        change walkInterior pXR = walkInterior pXR
        rfl
      by_cases hb2 : b = 2
      · subst b
        exact (hab rfl).elim
      have hb3 : b = 3 := by omega
      subst b
      change walkInterior pXZ = walkInterior pXZ
      rfl
    have ha3 : a = 3 := by omega
    subst a
    by_cases hb0 : b = 0
    · subst b
      change walkInterior pLZ.reverse = walkInterior pLZ
      exact walkInterior_reverse pLZ
    by_cases hb1 : b = 1
    · subst b
      change walkInterior pZR = walkInterior pZR
      rfl
    by_cases hb2 : b = 2
    · subst b
      change walkInterior pXZ.reverse = walkInterior pXZ
      exact walkInterior_reverse pXZ
    have hb3 : b = 3 := by omega
    subst b
    exact (hab rfl).elim
  have hEdgeDisjoint (e f : Sym2 (Fin 4)) (hef : e ≠ f) :
      Disjoint (edgeInterior e) (edgeInterior f) := by
    by_cases he01 : e = s(0, 1)
    · subst e
      simp [edgeInterior, hLRempty]
    by_cases he02 : e = s(0, 2)
    · subst e
      by_cases hf01 : f = s(0, 1)
      · subst f
        simp [edgeInterior, hLRempty]
      by_cases hf02 : f = s(0, 2)
      · exact (hef hf02.symm).elim
      by_cases hf12 : f = s(1, 2)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hLX_XR
      by_cases hf03 : f = s(0, 3)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hLX_LZ
      by_cases hf13 : f = s(1, 3)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hLX_ZR
      by_cases hf23 : f = s(2, 3)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hXZ_LX.symm
      simp [edgeInterior, hf01, hf02, hf12, hf03, hf13, hf23]
    by_cases he12 : e = s(1, 2)
    · subst e
      by_cases hf01 : f = s(0, 1)
      · subst f
        simp [edgeInterior, hLRempty]
      by_cases hf02 : f = s(0, 2)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hLX_XR.symm
      by_cases hf12 : f = s(1, 2)
      · exact (hef hf12.symm).elim
      by_cases hf03 : f = s(0, 3)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hXR_LZ
      by_cases hf13 : f = s(1, 3)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hXR_ZR
      by_cases hf23 : f = s(2, 3)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hXZ_XR.symm
      simp [edgeInterior, hf01, hf02, hf12, hf03, hf13, hf23]
    by_cases he03 : e = s(0, 3)
    · subst e
      by_cases hf01 : f = s(0, 1)
      · subst f
        simp [edgeInterior, hLRempty]
      by_cases hf02 : f = s(0, 2)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hLX_LZ.symm
      by_cases hf12 : f = s(1, 2)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hXR_LZ.symm
      by_cases hf03 : f = s(0, 3)
      · exact (hef hf03.symm).elim
      by_cases hf13 : f = s(1, 3)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hLZ_ZR
      by_cases hf23 : f = s(2, 3)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hXZ_LZ.symm
      simp [edgeInterior, hf01, hf02, hf12, hf03, hf13, hf23]
    by_cases he13 : e = s(1, 3)
    · subst e
      by_cases hf01 : f = s(0, 1)
      · subst f
        simp [edgeInterior, hLRempty]
      by_cases hf02 : f = s(0, 2)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hLX_ZR.symm
      by_cases hf12 : f = s(1, 2)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hXR_ZR.symm
      by_cases hf03 : f = s(0, 3)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hLZ_ZR.symm
      by_cases hf13 : f = s(1, 3)
      · exact (hef hf13.symm).elim
      by_cases hf23 : f = s(2, 3)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hXZ_ZR.symm
      simp [edgeInterior, hf01, hf02, hf12, hf03, hf13, hf23]
    by_cases he23 : e = s(2, 3)
    · subst e
      by_cases hf01 : f = s(0, 1)
      · subst f
        simp [edgeInterior, hLRempty]
      by_cases hf02 : f = s(0, 2)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hXZ_LX
      by_cases hf12 : f = s(1, 2)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hXZ_XR
      by_cases hf03 : f = s(0, 3)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hXZ_LZ
      by_cases hf13 : f = s(1, 3)
      · subst f
        simpa [edgeInterior, Sym2.eq_iff] using hXZ_ZR
      by_cases hf23 : f = s(2, 3)
      · exact (hef hf23.symm).elim
      simp [edgeInterior, hf01, hf02, hf12, hf03, hf13, hf23]
    simp [edgeInterior, he01, he02, he12, he03, he13, he23]
  refine ⟨
    { branch := branch
      route := route
      route_isPath := ?_
      branch_avoids_interiors := ?_
      route_interiors_disjoint := ?_ }⟩
  · intro a b hab
    exact hroutePath hab
  · intro a b hab w
    exact hrouteAvoids hab w
  · intro a b c d hab hcd hne
    rw [hrouteInterior hab, hrouteInterior hcd]
    apply hEdgeDisjoint
    intro heq
    exact hne (Sym2.eq_iff.mp heq)

end Lax16ThetaK4
end Lax16Proofs
