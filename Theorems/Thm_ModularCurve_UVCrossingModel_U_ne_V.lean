import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_U_ne_V

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.U_ne_V {W : Type*} [CommRing W] (π : W) [Nontrivial (W ⧸ Ideal.span {π})] : U π ≠ V π := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_U_ne_V.solution
