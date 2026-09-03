import Mathlib
import Definitions.Def_ModularCurve_UVCrossingChart
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_chartHom_X

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.chartHom_X {W : Type*} [CommRing W] (π : W) : chartHom π PowerSeries.X = S π := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_chartHom_X.solution
