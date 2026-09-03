import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma

set_option autoImplicit false

theorem LanglandsTunnell.exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma
    (d τ τ' : ℝ) :
    ∃ K R : ℝ, 0 < K ∧ ∀ y : ℝ, R ≤ y →
      ‖Complex.Gamma (((y + d : ℝ) : ℂ) + (τ' : ℂ) * Complex.I)‖
        ≤ K * y ^ d * ‖Complex.Gamma ((y : ℂ) + (τ : ℂ) * Complex.I)‖ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_forall_norm_Gamma_add_mul_I_le_mul_rpow_mul_norm_Gamma.solution
