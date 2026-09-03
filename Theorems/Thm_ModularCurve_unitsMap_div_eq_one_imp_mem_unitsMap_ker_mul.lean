import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_unitsMap_div_eq_one_imp_mem_unitsMap_ker_mul

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.unitsMap_div_eq_one_imp_mem_unitsMap_ker_mul (q M₀ : ℕ) [Fact q.Prime] [NeZero M₀]
    (hpM : q ∣ M₀ * q) (u : (ZMod (M₀ * q))ˣ) (hu : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1) :
    u ∈ (ZMod.unitsMap (dvd_mul_right M₀ q)).ker := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_unitsMap_div_eq_one_imp_mem_unitsMap_ker_mul.solution
