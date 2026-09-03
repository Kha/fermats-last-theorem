import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_isAdicComplete_maximalIdeal

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.isAdicComplete_maximalIdeal
    {Ô : Type*} [CommRing Ô] [IsLocalRing Ô] [IsNoetherianRing Ô]
    [IsAdicComplete (IsLocalRing.maximalIdeal Ô) Ô] (π : Ô)
    [IsLocalRing (UVCrossingModel Ô π)] :
    IsAdicComplete (IsLocalRing.maximalIdeal (UVCrossingModel Ô π)) (UVCrossingModel Ô π) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_isAdicComplete_maximalIdeal.solution
