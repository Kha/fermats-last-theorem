import Mathlib
import Definitions.Def_ModularCurve_UVCrossingInitialForm
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_eq_unit_mul_U_pow_mul_V_pow_mul_const_pow_of_sInf_eq_sSup

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

theorem ModularCurve.UVCrossingModel.exists_eq_unit_mul_U_pow_mul_V_pow_mul_const_pow_of_sInf_eq_sSup
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (y : UVCrossingModel W (ϖ ^ e)) (hy : y ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (haby : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = y)
    (h : sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) =
      sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab)) :
    ∃ (w : (UVCrossingModel W (ϖ ^ e))ˣ) (a b n : ℕ), (a = 0 ∨ b = 0) ∧
      y = w * U (ϖ ^ e) ^ a * V (ϖ ^ e) ^ b * const (ϖ ^ e) ϖ ^ n := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_eq_unit_mul_U_pow_mul_V_pow_mul_const_pow_of_sInf_eq_sSup.solution
