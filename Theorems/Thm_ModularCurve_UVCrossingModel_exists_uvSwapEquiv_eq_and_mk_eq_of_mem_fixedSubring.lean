import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_uvSwapEquiv_eq_and_mk_eq_of_mem_fixedSubring

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.exists_uvSwapEquiv_eq_and_mk_eq_of_mem_fixedSubring {W : Type*} [CommRing W] {π : W} (hreg : ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C π) ∈ nonZeroDivisors (MvPowerSeries (Fin 2) W)) {x : UVCrossingModel W π} (hx : x ∈ fixedSubring π) : ∃ F : MvPowerSeries (Fin 2) W, uvSwapEquiv F = F ∧ UVCrossingModel.mk π F = x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_uvSwapEquiv_eq_and_mk_eq_of_mem_fixedSubring.solution
