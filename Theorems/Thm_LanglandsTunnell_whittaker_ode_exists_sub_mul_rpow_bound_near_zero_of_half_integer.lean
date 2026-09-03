import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer

set_option autoImplicit false

open Real Complex Filter Topology

theorem LanglandsTunnell.whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer
    (n : ℕ) (hn : 1 ≤ n) (ν : ℂ) (hν : ν = (n : ℂ) / 2) (κ : ℝ) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((κ : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0) :
    ∃ (c : ℂ) (δ : ℝ), 0 < δ ∧
      (∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        ‖f y - c * (y : ℂ) ^ (1 / 2 - ν)‖ ≤ C * y ^ (1 / 2 - (n : ℝ) / 2 + δ)) ∧
      (c = 0 →
        (∃ L : ℂ, Tendsto (fun y : ℝ => (y : ℂ) ^ (-(1 / 2 + ν)) * f y) (𝓝[>] 0) (𝓝 L)) ∧
        Tendsto (fun y : ℝ => (y : ℂ) ^ (1 / 2 - ν) * (deriv f y - (1 / 2 + ν) / (y : ℂ) * f y)) (𝓝[>] 0) (𝓝 0) ∧
        ∃ C' : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C' * y ^ (1 / 2 + (n : ℝ) / 2)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_whittaker_ode_exists_sub_mul_rpow_bound_near_zero_of_half_integer.solution
