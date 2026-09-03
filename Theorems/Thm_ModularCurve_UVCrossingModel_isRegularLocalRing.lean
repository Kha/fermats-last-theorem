import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_isRegularLocalRing

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.isRegularLocalRing {W : Type*} [CommRing W] [IsNoetherianRing W] [IsLocalRing W] [IsDomain W] {π : W} (hW : IsLocalRing.maximalIdeal W = Ideal.span {π}) (hπ0 : π ≠ 0) : IsRegularLocalRing (UVCrossingModel W π) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_isRegularLocalRing.solution
