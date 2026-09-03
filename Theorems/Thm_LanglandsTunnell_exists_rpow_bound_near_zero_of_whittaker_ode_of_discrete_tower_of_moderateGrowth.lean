import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth

set_option autoImplicit false

theorem LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth
    (n m : ℕ) (k : ℝ) (ν : ℂ) (hk : k = n + 1 + 2 * m) (hν : ν = (n : ℂ) / 2) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ δ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth.solution
