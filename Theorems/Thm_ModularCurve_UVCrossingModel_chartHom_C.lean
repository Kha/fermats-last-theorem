import Mathlib
import Definitions.Def_ModularCurve_UVCrossingChart
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_chartHom_C

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.chartHom_C {W : Type*} [CommRing W] (π : W) (w : W) : chartHom π (PowerSeries.C w) = const π w := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_chartHom_C.solution
