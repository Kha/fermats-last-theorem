import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_eq_unit_mul_U_pow_mul_V_pow_mul_const_pow_of_dvd
set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.exists_eq_unit_mul_U_pow_mul_V_pow_mul_const_pow_of_dvd
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    {r : UVCrossingModel W (ϖ ^ e)} {m : ℕ} (hr : r ∣ const (ϖ ^ e) ϖ ^ m) :
    ∃ (w : (UVCrossingModel W (ϖ ^ e))ˣ) (a b n : ℕ), (a = 0 ∨ b = 0) ∧
      r = w * U (ϖ ^ e) ^ a * V (ϖ ^ e) ^ b * const (ϖ ^ e) ϖ ^ n := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_eq_unit_mul_U_pow_mul_V_pow_mul_const_pow_of_dvd.solution
