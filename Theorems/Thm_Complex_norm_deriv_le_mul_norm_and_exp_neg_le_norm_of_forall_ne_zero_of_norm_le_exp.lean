import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp

set_option autoImplicit false

theorem Complex.norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp
    (F : ℂ → ℂ) (s₀ : ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (hd : DifferentiableOn ℂ F (Metric.ball s₀ R))
    (hnz : ∀ z ∈ Metric.ball s₀ R, F z ≠ 0)
    (hup : ∀ z ∈ Metric.ball s₀ R, ‖F z‖ ≤ Real.exp M)
    (hlo : Real.exp (-M) ≤ ‖F s₀‖) :
    ∀ s ∈ Metric.closedBall s₀ (R / 2),
      ‖deriv F s‖ ≤ 48 * M / R * ‖F s‖ ∧ Real.exp (-(5 * M)) ≤ ‖F s‖ := by p2m_exact_reverting @_root_.P2MW.S_Complex_norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp.solution
