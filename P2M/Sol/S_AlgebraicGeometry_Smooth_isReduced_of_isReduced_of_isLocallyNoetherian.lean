import Mathlib
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace REDsol

theorem geometricallyReduced_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] : GeometricallyReduced f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  haveI : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h inferInstance
  exact AlgebraicGeometry.isReduced_of_smooth_of_field snd

end REDsol

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsReduced Y] [IsLocallyNoetherian Y] :
    IsReduced X := by
  haveI := REDsol.geometricallyReduced_of_smooth f
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f
