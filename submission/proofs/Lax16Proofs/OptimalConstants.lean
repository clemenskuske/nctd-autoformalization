import Lax16.OptimalConstants
import Lax16.OuterplanarBound
import Lax16.OuterplanarSharpness
import Lax16.PlanarBound
import Lax16.PlanarSharpness

namespace Lax16Proofs.OptimalConstants

open Lax16.PlanarGraphs
open Lax16.TeachingMaps

universe u

/--
---
conclusion: Lax16.OptimalConstants.optimal_radius_one_constants
assumptions:
  - Lax16.PlanarBound.positiveNCTD_le_four
  - Lax16.PlanarSharpness.planar_bound_is_sharp
  - Lax16.OuterplanarBound.positiveNCTD_le_two
  - Lax16.OuterplanarSharpness.outerplanar_bound_is_sharp
---
The universal bounds are the planar and outerplanar upper-bound theorems.
Their respective sharp examples supply the two existential conjuncts.
-/
theorem optimal_radius_one_constants :
    (∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      IsPlanar G → positiveNCTD G 1 ≤ 4) ∧
    (∃ G : SimpleGraph (Fin 5),
      IsPlanar G ∧ positiveNCTD G 1 = 4) ∧
    (∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      IsOuterplanar G → positiveNCTD G 1 ≤ 2) ∧
    ∃ G : SimpleGraph (Fin 6),
      IsOuterplanar G ∧ positiveNCTD G 1 = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V _ G hplanar
    exact Lax16.PlanarBound.positiveNCTD_le_four G hplanar
  · exact ⟨Lax16.PlanarSharpness.sharpPlanarGraph,
      Lax16.PlanarSharpness.planar_bound_is_sharp⟩
  · intro V _ G houter
    exact Lax16.OuterplanarBound.positiveNCTD_le_two G houter
  · refine ⟨Lax16.OuterplanarSharpness.sharpOuterplanarGraph, ?_⟩
    exact ⟨Lax16.OuterplanarSharpness.outerplanar_bound_is_sharp.1,
      Lax16.OuterplanarSharpness.outerplanar_bound_is_sharp.2.2⟩

end Lax16Proofs.OptimalConstants
