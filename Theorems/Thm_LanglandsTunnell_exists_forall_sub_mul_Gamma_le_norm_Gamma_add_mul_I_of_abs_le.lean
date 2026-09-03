import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_forall_sub_mul_Gamma_le_norm_Gamma_add_mul_I_of_abs_le

set_option autoImplicit false

open Complex

theorem LanglandsTunnell.exists_forall_sub_mul_Gamma_le_norm_Gamma_add_mul_I_of_abs_le
    (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ σ τ : ℝ, R ≤ σ → |τ| ≤ K →
      (1 - ε) * Real.Gamma σ ≤ ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ∧
      ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ Real.Gamma σ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_forall_sub_mul_Gamma_le_norm_Gamma_add_mul_I_of_abs_le.solution
