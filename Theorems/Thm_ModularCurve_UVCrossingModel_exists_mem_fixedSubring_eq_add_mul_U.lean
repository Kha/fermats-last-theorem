import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_mem_fixedSubring_eq_add_mul_U

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.exists_mem_fixedSubring_eq_add_mul_U {W : Type*} [CommRing W] (π : W) (x : UVCrossingModel W π) : ∃ a b : UVCrossingModel W π, a ∈ fixedSubring π ∧ b ∈ fixedSubring π ∧ x = a + b * U π := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_mem_fixedSubring_eq_add_mul_U.solution
