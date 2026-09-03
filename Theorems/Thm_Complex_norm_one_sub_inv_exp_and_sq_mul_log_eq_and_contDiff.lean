import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_norm_one_sub_inv_exp_and_sq_mul_log_eq_and_contDiff

set_option autoImplicit false

theorem Complex.norm_one_sub_inv_exp_and_sq_mul_log_eq_and_contDiff :
    (∀ X Θ : ℝ, ‖(1 : ℂ) - (Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ)))⁻¹‖ =
        Real.exp (-(X / 2)) * ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖) ∧
    (∀ X Θ : ℝ, ‖(1 : ℂ) - (Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ)))⁻¹‖ ^ 2 *
          Real.log ‖(1 : ℂ) - (Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ)))⁻¹‖ =
        Real.exp (-X) *
          (‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ ^ 2 *
              Real.log ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ -
            X / 2 * ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ ^ 2)) ∧
    (∀ X Θ : ℝ, ‖(1 : ℂ) - Complex.exp (((X / 2 : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (Θ : ℂ))‖ ^ 2 =
        1 - 2 * Real.exp (X / 2) * Real.cos (2 * Real.pi * Θ) + Real.exp X) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => 1 - 2 * Real.exp (p.1 / 2) * Real.cos (2 * Real.pi * p.2) + Real.exp p.1) := by p2m_exact_reverting @_root_.P2MW.S_Complex_norm_one_sub_inv_exp_and_sq_mul_log_eq_and_contDiff.solution
