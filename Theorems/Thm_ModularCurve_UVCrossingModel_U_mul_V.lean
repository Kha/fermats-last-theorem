import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_U_mul_V

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.U_mul_V {W : Type*} [CommRing W] (π : W) : U π * V π = const π π := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_U_mul_V.solution
