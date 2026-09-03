import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_neg_re_deriv_div_le_sub_sum_re_inv_sub_of_norm_le_exp_of_ne_zero_of_lt_re

set_option autoImplicit false

theorem Complex.neg_re_deriv_div_le_sub_sum_re_inv_sub_of_norm_le_exp_of_ne_zero_of_lt_re
    (f : ℂ → ℂ) (s₀ : ℂ) (r M : ℝ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall s₀ r)) (h₀ : f s₀ ≠ 0)
    (hM : ∀ s ∈ Metric.closedBall s₀ r, ‖f s‖ ≤ Real.exp M * ‖f s₀‖)
    (hne : ∀ s ∈ Metric.closedBall s₀ (r / 2), s₀.re < s.re → f s ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, ρ ∈ Metric.closedBall s₀ (r / 2) ∧ f ρ = 0) :
    -(deriv f s₀ / f s₀).re ≤ 8 * (M + 1) / r - ∑ ρ ∈ Z, ((s₀ - ρ)⁻¹).re := by p2m_exact_reverting @_root_.P2MW.S_Complex_neg_re_deriv_div_le_sub_sum_re_inv_sub_of_norm_le_exp_of_ne_zero_of_lt_re.solution
