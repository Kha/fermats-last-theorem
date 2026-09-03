import Mathlib
import Definitions.Def_ModularCurve_UVCrossingChart
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_crossingSwap_chartHom

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.crossingSwap_chartHom {W : Type*} [CommRing W] (π : W) (f : PowerSeries W) : crossingSwap π (chartHom π f) = chartHom π f := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_crossingSwap_chartHom.solution
