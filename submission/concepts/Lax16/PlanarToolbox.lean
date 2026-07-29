import Lax16.PlanarGraphs

/-!
---
title: Neighbor layers of planar graphs are outerplanar
type: theorem
---
For a vertex `v` in a planar graph, delete `v` from a plane drawing and use
the face formerly incident with `v` as the outer face.  Every neighbor of
`v` lies on that face, so the graph induced by the open neighborhood of `v`
is outerplanar.

Under the forbidden-subdivision definitions of this submission, the same
fact says that a topological `K₄` or `K₂,₃` in the neighbor layer would,
together with `v`, produce a topological `K₅` or `K₃,₃` in the original
graph.
-/

namespace Lax16.PlanarToolbox

open Lax16.PlanarGraphs

universe u

/-- The graph induced by the open neighborhood of a planar vertex is outerplanar. -/
axiom neighbor_layer_outerplanar {V : Type u} {G : SimpleGraph V}
    (hplanar : IsPlanar G) (v : V) :
    IsOuterplanar (G.induce (G.neighborSet v))

end Lax16.PlanarToolbox
