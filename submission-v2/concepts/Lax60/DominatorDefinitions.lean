import Lax60.TeachingMaps

/-!
---
title: Active dominators and their local teaching assignments
type: definition
---
A neighbor `w` dominates a center `v` when the closed neighborhood of `v` is
contained in that of `w`.  It is active when the two closed neighborhoods are
different.  A valid dominator teaching set has at most four labels, contains
the center anchor, is positive for the dominator, and separates the dominator
from every distinct non-active concept in the center's closed neighborhood.
The family condition handles pairs of active dominators using labels from
either teaching set, as required by no-clash.
-/

namespace Lax60.DominatorDefinitions

open Lax60.TeachingMaps

universe u

/-- The neighboring dominators of a center vertex. -/
def dominatorSet {V : Type u} (G : SimpleGraph V) (v : V) : Set V :=
  {w | G.Adj v w ∧ Dominates G 1 v w}

/-- A dominator whose closed neighborhood is genuinely different from the center's. -/
def IsActiveDominator {V : Type u} (G : SimpleGraph V)
    (v w : V) : Prop :=
  w ∈ dominatorSet G v ∧ DistinctConcepts G 1 v w

/--
A width-four anchored teaching set that handles every non-active concept in
the center ball.  Active dominator pairs are handled symmetrically by
`CompletesActiveDominators`.
-/
def IsDominatorTeachingSet {V : Type u} (G : SimpleGraph V)
    (v w : V) (S : Finset V) : Prop :=
  S.card ≤ 4 ∧
  v ∈ S ∧
  (∀ x ∈ S, x ∈ closedBall G 1 w) ∧
  ∀ z : V, z ∈ closedBall G 1 v →
    DistinctConcepts G 1 w z →
    ¬ IsActiveDominator G v z →
      ∃ x ∈ S, x ∉ closedBall G 1 z

/--
A family valid for every active dominator, with every active pair separated
by the union of its two teaching sets.
-/
def CompletesActiveDominators {V : Type u} (G : SimpleGraph V)
    (v : V) (T : TeachingMap V 1) : Prop :=
  (∀ w : V, IsActiveDominator G v w →
    IsDominatorTeachingSet G v w (T w)) ∧
  ∀ w z : V, IsActiveDominator G v w →
    IsActiveDominator G v z →
    DistinctConcepts G 1 w z →
      Separates G 1 T w z

/-- An outside vertex adjacent to all three selected neighbors. -/
def OutsideSees {V : Type u} (G : SimpleGraph V)
    (v : V) (Y : Finset V) (x : V) : Prop :=
  x ∉ closedBall G 1 v ∧ ∀ y ∈ Y, G.Adj x y

end Lax60.DominatorDefinitions
