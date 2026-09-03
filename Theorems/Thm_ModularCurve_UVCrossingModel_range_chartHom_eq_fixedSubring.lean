import Mathlib
import Definitions.Def_ModularCurve_UVCrossingChart
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_range_chartHom_eq_fixedSubring

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.range_chartHom_eq_fixedSubring {W : Type*} [CommRing W] {π : W} [IsPrecomplete (Ideal.span {π}) W] (hreg : ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C π) ∈ nonZeroDivisors (MvPowerSeries (Fin 2) W)) (hsep : ∀ x : UVCrossingModel W π, (∀ B : ℕ, x ∈ Ideal.span {const π π} ^ B) → x = 0) : (chartHom π).range = fixedSubring π := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_range_chartHom_eq_fixedSubring.solution
