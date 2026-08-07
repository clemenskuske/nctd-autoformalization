import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Nat.Lattice

/-!
---
title: No-clash teaching for closed graph balls
type: definition
---
A vertex `v` of a finite simple graph represents its closed ball of radius
`k`: the vertices reachable from `v` by a walk of length at most `k`.

A teaching map assigns a finite set of labels to every vertex.  It is
no-clash when every two distinct radius-`k` balls are distinguished by a
label used by at least one of their teaching sets.  It is positive when every
label assigned to `v` lies in the ball represented by `v`.

The ordinary and positive no-clash teaching dimensions are the least uniform
widths of such maps.  All subsequent results in this submission specialize
these definitions to `k = 1`, where the represented balls are precisely the
closed neighborhoods of the draft.
-/

namespace Lax16.TeachingMaps

universe u

/-- The closed radius-`k` ball around `v`, expressed by bounded walk length. -/
def closedBall {V : Type u} (G : SimpleGraph V) (k : ℕ) (v : V) : Set V :=
  {w | ∃ p : G.Walk v w, p.length ≤ k}

/-- The closed radius-`k` ball as a finset when the vertex type is finite. -/
noncomputable def closedBallFinset {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun w => w ∈ closedBall G k v

/--
A radius-`k` teaching map assigns a finite set of vertex labels to each
radius-`k` concept.  The index makes the represented neighborhood size
explicit in every later interface.
-/
abbrev TeachingMap (V : Type u) (_k : ℕ) := V → Finset V

/-- Two vertices represent distinct concepts at radius `k`. -/
def DistinctConcepts {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (v w : V) : Prop :=
  closedBall G k v ≠ closedBall G k w

/-- A label witnesses one of the two sides of the symmetric difference. -/
def IsWitness {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (x v w : V) : Prop :=
  x ∈ closedBall G k v ∧ x ∉ closedBall G k w

/-- The teaching sets of `v` and `w` contain a label on which their concepts differ. -/
def Separates {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (T : TeachingMap V k) (v w : V) : Prop :=
  ∃ x : V, (x ∈ T v ∨ x ∈ T w) ∧
    (IsWitness G k x v w ∨ IsWitness G k x w v)

/-- Every pair of distinct concepts is separated. -/
def IsNoClash {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (T : TeachingMap V k) : Prop :=
  ∀ ⦃v w : V⦄, DistinctConcepts G k v w → Separates G k T v w

/-- Every teaching label is positive for the concept receiving it. -/
def IsPositive {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (T : TeachingMap V k) : Prop :=
  ∀ ⦃v x : V⦄, x ∈ T v → x ∈ closedBall G k v

/-- Every teaching set has cardinality at most `d`. -/
def HasWidthAtMost {V : Type u} {k : ℕ}
    (T : TeachingMap V k) (d : ℕ) : Prop :=
  ∀ v : V, (T v).card ≤ d

/-- Every teaching set is nonempty. -/
def HasNonemptySets {V : Type u} {k : ℕ} (T : TeachingMap V k) : Prop :=
  ∀ v : V, (T v).Nonempty

/-- There is a radius-`k` no-clash teaching map of width at most `d`. -/
def HasNCTDAtMost {V : Type u} (G : SimpleGraph V) (k d : ℕ) : Prop :=
  ∃ T : TeachingMap V k, IsNoClash G k T ∧ HasWidthAtMost T d

/-- There is a positive radius-`k` no-clash teaching map of width at most `d`. -/
def HasPositiveNCTDAtMost {V : Type u} (G : SimpleGraph V)
    (k d : ℕ) : Prop :=
  ∃ T : TeachingMap V k,
    IsPositive G k T ∧ IsNoClash G k T ∧ HasWidthAtMost T d

/-- The no-clash teaching dimension for closed balls of radius `k`. -/
noncomputable def nctd {V : Type u} (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sInf {d : ℕ | HasNCTDAtMost G k d}

/-- The positive no-clash teaching dimension for closed balls of radius `k`. -/
noncomputable def positiveNCTD {V : Type u}
    (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sInf {d : ℕ | HasPositiveNCTDAtMost G k d}

/-- The radius-`k` ball of `v` is contained in that of `w`. -/
def Dominates {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (v w : V) : Prop :=
  closedBall G k v ⊆ closedBall G k w

/-- Replace the teaching set at `target` by the set at `source`. -/
noncomputable def copyTeachingSet {V : Type u} {k : ℕ} (T : TeachingMap V k)
    (source target : V) : TeachingMap V k := by
  classical
  exact fun v => if v = target then T source else T v

end Lax16.TeachingMaps
