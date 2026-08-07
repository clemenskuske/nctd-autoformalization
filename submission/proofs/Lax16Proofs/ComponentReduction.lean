import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Lax16.TeachingMaps

namespace Lax16Proofs.ComponentReduction

open Lax16.TeachingMaps

universe u

/--
Choose a teaching map on each component and map all of its labels into the
ambient vertex type.  Labels and radius-one balls transport across the
component inclusion.  Vertices in different components are separated by any
label in the nonempty teaching set on the first component.
-/
theorem combine_components {V : Type u} [Fintype V]
    (G : SimpleGraph V) (d : ℕ)
    (hcomponents :
      ∀ C : G.ConnectedComponent,
        ∃ T : TeachingMap C 1,
          IsPositive C.toSimpleGraph 1 T ∧
          IsNoClash C.toSimpleGraph 1 T ∧
          HasWidthAtMost T d ∧
          HasNonemptySets T) :
    HasPositiveNCTDAtMost G 1 d := by
  classical
  choose T hpositive hnoclash hwidth hnonempty using hcomponents

  have ball_to_ambient
      (C : G.ConnectedComponent) (a b : C)
      (h : b ∈ closedBall C.toSimpleGraph 1 a) :
      (b : V) ∈ closedBall G 1 (a : V) := by
    obtain ⟨p, hp⟩ := h
    refine ⟨p.map C.toSimpleGraph_hom, ?_⟩
    calc
      (p.map C.toSimpleGraph_hom).length = p.length :=
        SimpleGraph.Walk.length_map C.toSimpleGraph_hom p
      _ ≤ 1 := hp

  have ball_to_component
      (C : G.ConnectedComponent) (a b : C)
      (h : (b : V) ∈ closedBall G 1 (a : V)) :
      b ∈ closedBall C.toSimpleGraph 1 a := by
    obtain ⟨p, hp⟩ := h
    have hlength : p.length = 0 ∨ p.length = 1 := by omega
    rcases hlength with hzero | hone
    · have hab : a = b := Subtype.ext (p.eq_of_length_eq_zero hzero)
      subst b
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
    · have hab : C.toSimpleGraph.Adj a b :=
        (C.toSimpleGraph_adj a.property b.property).2
          (p.adj_of_length_eq_one hone)
      exact ⟨hab.toWalk, by simp⟩

  have map_mem_transport
      (C D : G.ConnectedComponent) (hCD : C = D)
      (a y : C) (b : D) (hab : (a : V) = (b : V))
      (hy : y ∈ T C a) :
      (y : V) ∈
        (T D b).map ⟨Subtype.val, Subtype.val_injective⟩ := by
    subst D
    have hab' : a = b := Subtype.ext hab
    subst b
    exact Finset.mem_map.mpr ⟨y, hy, rfl⟩

  let componentVertex (v : V) : G.connectedComponentMk v :=
    ⟨v, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  let globalMap : TeachingMap V 1 := fun v =>
    (T (G.connectedComponentMk v) (componentVertex v)).map
      ⟨Subtype.val, Subtype.val_injective⟩

  refine ⟨globalMap, ?_, ?_, ?_⟩
  · intro v x hx
    simp only [globalMap, Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ball_to_ambient (G.connectedComponentMk v) (componentVertex v) y
      (hpositive (G.connectedComponentMk v) hy)
  · intro v w hdifferent
    by_cases hcomponent :
        G.connectedComponentMk v = G.connectedComponentMk w
    · let C := G.connectedComponentMk v
      let vv : C := componentVertex v
      let ww : C := ⟨w, hcomponent.symm⟩
      have hlocalDistinct :
          DistinctConcepts C.toSimpleGraph 1 vv ww := by
        intro hequal
        apply hdifferent
        ext x
        constructor
        · intro hx
          obtain ⟨p, hp⟩ := hx
          let xx : C :=
            ⟨x, (SimpleGraph.ConnectedComponent.sound
              (SimpleGraph.Walk.reachable p)).symm⟩
          have hlocal : xx ∈ closedBall C.toSimpleGraph 1 vv :=
            ball_to_component C vv xx ⟨p, hp⟩
          rw [hequal] at hlocal
          exact ball_to_ambient C ww xx hlocal
        · intro hx
          obtain ⟨p, hp⟩ := hx
          let xx : C :=
            ⟨x, (SimpleGraph.ConnectedComponent.sound
              (SimpleGraph.Walk.reachable p)).symm.trans hcomponent.symm⟩
          have hlocal : xx ∈ closedBall C.toSimpleGraph 1 ww :=
            ball_to_component C ww xx ⟨p, hp⟩
          rw [← hequal] at hlocal
          exact ball_to_ambient C vv xx hlocal
      obtain ⟨y, hy, hwitness⟩ :=
        hnoclash C hlocalDistinct
      refine ⟨(y : V), ?_, ?_⟩
      · rcases hy with hy | hy
        · left
          exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
        · right
          simp only [globalMap]
          exact map_mem_transport C (G.connectedComponentMk w)
            hcomponent ww y (componentVertex w) rfl hy
      · rcases hwitness with hwitness | hwitness
        · left
          exact ⟨ball_to_ambient C vv y hwitness.1,
            fun h => hwitness.2 (ball_to_component C ww y h)⟩
        · right
          exact ⟨ball_to_ambient C ww y hwitness.1,
            fun h => hwitness.2 (ball_to_component C vv y h)⟩
    · let C := G.connectedComponentMk v
      let vv : C := componentVertex v
      obtain ⟨y, hy⟩ := hnonempty C vv
      refine ⟨(y : V), ?_, Or.inl ?_⟩
      · left
        exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
      · refine ⟨ball_to_ambient C vv y (hpositive C hy), ?_⟩
        intro hball
        obtain ⟨p, _⟩ := hball
        apply hcomponent
        calc
          G.connectedComponentMk v = G.connectedComponentMk (y : V) :=
            y.property.symm
          _ = G.connectedComponentMk w :=
            (SimpleGraph.ConnectedComponent.sound
              (SimpleGraph.Walk.reachable p)).symm
  · intro v
    simpa [globalMap] using hwidth (G.connectedComponentMk v) (componentVertex v)

end Lax16Proofs.ComponentReduction
