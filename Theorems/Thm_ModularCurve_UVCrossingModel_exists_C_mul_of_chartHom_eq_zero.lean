import Mathlib
import Definitions.Def_ModularCurve_UVCrossingChart
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_C_mul_of_chartHom_eq_zero

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.exists_C_mul_of_chartHom_eq_zero {W : Type*} [CommRing W] {π : W} {f : PowerSeries W} (hf : chartHom π f = 0) : ∃ g : PowerSeries W, f = PowerSeries.C π * g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_C_mul_of_chartHom_eq_zero.solution
