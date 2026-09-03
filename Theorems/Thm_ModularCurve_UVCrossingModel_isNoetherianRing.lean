import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_isNoetherianRing

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.isNoetherianRing {W : Type*} [CommRing W] [IsNoetherianRing W] (π : W) : IsNoetherianRing (UVCrossingModel W π) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_isNoetherianRing.solution
