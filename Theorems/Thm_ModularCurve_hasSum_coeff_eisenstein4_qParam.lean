import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_hasSum_coeff_eisenstein4_qParam
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.hasSum_coeff_eisenstein4_qParam (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m eisenstein4 : ℤ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (ModularForm.E₄ τ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasSum_coeff_eisenstein4_qParam.solution
