import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_U_quadratic

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.U_quadratic {W : Type*} [CommRing W] (π : W) : U π ^ 2 - S π * U π + const π π = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_U_quadratic.solution
