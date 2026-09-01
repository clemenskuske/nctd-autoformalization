import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
---
title: Planar and outerplanar finite simple graphs
type: definition
---
A topological model of a graph `H` in a graph `G` maps the vertices of `H`
injectively to branch vertices of `G` and maps every edge of `H` to a path in
`G`.  Path interiors contain no branch vertices and interiors belonging to
distinct edges are disjoint.

For finite simple graphs, planarity is encoded by Kuratowski's
characterization: neither `K₅` nor `K₃,₃` has a topological model.
Outerplanarity is encoded by the analogous characterization excluding
topological models of `K₄` and `K₂,₃`.
-/

namespace Lax60.PlanarGraphs

universe u v

/-- The internal vertices of a walk, with both endpoints removed. -/
def walkInterior {V : Type u} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) : Set V :=
  {x | x ∈ p.support ∧ x ≠ a ∧ x ≠ b}

/--
A subdivision model of `H` in `G`: distinct branch vertices joined by
internally vertex-disjoint paths corresponding to the edges of `H`.
-/
structure TopologicalModel {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- The injective map from vertices of `H` to branch vertices of `G`. -/
  branch : W ↪ V
  /-- The path representing each oriented edge of `H`. -/
  route : ∀ {a b : W}, H.Adj a b → G.Walk (branch a) (branch b)
  /-- Every route is a graph-theoretic path. -/
  route_isPath : ∀ {a b : W} (h : H.Adj a b), (route h).IsPath
  /-- No branch vertex occurs internally on an edge route. -/
  branch_avoids_interiors :
    ∀ {a b : W} (h : H.Adj a b) (w : W),
      branch w ∉ walkInterior (route h)
  /-- Routes representing distinct undirected edges have disjoint interiors. -/
  route_interiors_disjoint :
    ∀ {a b c d : W} (hab : H.Adj a b) (hcd : H.Adj c d),
      ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
        Disjoint (walkInterior (route hab)) (walkInterior (route hcd))

/-- `H` occurs as a subdivision in `G`. -/
def HasTopologicalModel {W : Type u} {V : Type v}
    (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (TopologicalModel H G)

/-- Planarity via exclusion of subdivisions of `K₅` and `K₃,₃`. -/
def IsPlanar {V : Type v} (G : SimpleGraph V) : Prop :=
  ¬ HasTopologicalModel (⊤ : SimpleGraph (Fin 5)) G ∧
  ¬ HasTopologicalModel
    (completeBipartiteGraph (Fin 3) (Fin 3)) G

/-- Outerplanarity via exclusion of subdivisions of `K₄` and `K₂,₃`. -/
def IsOuterplanar {V : Type v} (G : SimpleGraph V) : Prop :=
  ¬ HasTopologicalModel (⊤ : SimpleGraph (Fin 4)) G ∧
  ¬ HasTopologicalModel
    (completeBipartiteGraph (Fin 2) (Fin 3)) G

/--
A graph is two-connected when it has at least three vertices and remains
connected after deletion of any single vertex.
-/
def IsTwoConnected {V : Type v} (G : SimpleGraph V) : Prop :=
  3 ≤ Nat.card V ∧
  ∀ v : V, (G.induce {w : V | w ≠ v}).Connected

end Lax60.PlanarGraphs
