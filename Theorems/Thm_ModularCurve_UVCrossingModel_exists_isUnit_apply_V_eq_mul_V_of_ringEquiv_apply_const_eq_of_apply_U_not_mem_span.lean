import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_isUnit_apply_V_eq_mul_V_of_ringEquiv_apply_const_eq_of_apply_U_not_mem_span

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.exists_isUnit_apply_V_eq_mul_V_of_ringEquiv_apply_const_eq_of_apply_U_not_mem_span
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (θ : UVCrossingModel W (ϖ ^ e) ≃+* UVCrossingModel W (ϖ ^ e))
    (hθϖ : θ (const (ϖ ^ e) ϖ) = const (ϖ ^ e) ϖ)
    (hθU : θ (U (ϖ ^ e)) ∉ Ideal.span {V (ϖ ^ e), const (ϖ ^ e) ϖ}) :
    ∃ t : UVCrossingModel W (ϖ ^ e), IsUnit t ∧ θ (V (ϖ ^ e)) = t * V (ϖ ^ e) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_isUnit_apply_V_eq_mul_V_of_ringEquiv_apply_const_eq_of_apply_U_not_mem_span.solution
