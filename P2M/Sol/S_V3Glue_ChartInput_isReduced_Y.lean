import Mathlib
import Definitions.Def_AlgebraicGeometry_ResolvedModelGlueComponents
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import P2M.Util
namespace P2MW.S_V3Glue_ChartInput_isReduced_Y

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution {X : Scheme.{0}} {N : Type} (C : V3Glue.ChartInput X N) (n : N)
    [IsReduced (C.Res n)] [IsLocallyNoetherian (C.Res n)] : IsReduced (C.Y n) := by
  haveI : Etale (C.g n) := MorphismProperty.pullback_snd _ _ inferInstance
  exact Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (C.g n)
