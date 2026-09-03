import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_whittaker_ode_exists_sub_log_mul_sqrt_bound_near_zero_of_zero

set_option autoImplicit false

open Real Complex Filter Topology

theorem LanglandsTunnell.whittaker_ode_exists_sub_log_mul_sqrt_bound_near_zero_of_zero
    (κ : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - (0 : ℂ) ^ 2 + 2 * (π : ℂ) * ((κ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) :
    ∃ (a b : ℂ) (δ : ℝ), 0 < δ ∧
      (∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖f y - (a + b * (Real.log y : ℂ)) * (Real.sqrt y : ℂ)‖ ≤ C * y ^ (1 / 2 + δ)) ∧
      (b = 0 →
        Tendsto (fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ)⁻¹ * f y) (𝓝[>] 0) (𝓝 a) ∧
        Tendsto (fun y : ℝ => ((Real.sqrt y : ℝ) : ℂ) * (deriv f y - f y / (2 * (y : ℂ)))) (𝓝[>] 0) (𝓝 0)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_whittaker_ode_exists_sub_log_mul_sqrt_bound_near_zero_of_zero.solution
