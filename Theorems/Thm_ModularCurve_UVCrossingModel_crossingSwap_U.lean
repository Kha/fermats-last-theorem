import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_crossingSwap_U

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.crossingSwap_U {W : Type*} [CommRing W] (π : W) : crossingSwap π (U π) = V π := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_crossingSwap_U.solution
