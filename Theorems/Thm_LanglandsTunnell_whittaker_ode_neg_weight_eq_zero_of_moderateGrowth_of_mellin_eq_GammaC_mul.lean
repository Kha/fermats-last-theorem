import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_whittaker_ode_neg_weight_eq_zero_of_moderateGrowth_of_mellin_eq_GammaC_mul

set_option autoImplicit false

open Real Complex

theorem LanglandsTunnell.whittaker_ode_neg_weight_eq_zero_of_moderateGrowth_of_mellin_eq_GammaC_mul
    (n : ℕ) (ν : ℂ) (hν : ν = (n : ℂ) / 2) (k : ℝ) (hk : 0 < k) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((-k : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N)
    (σ₀ : ℝ) (Ψ : ℂ → ℂ) (hΨ : Differentiable ℂ Ψ)
    (hmel : ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent (fun y : ℝ => f y) s ∧ mellin (fun y : ℝ => f y) s = Complex.Gammaℂ (s + 1 / 2 + ν) * Ψ s)
    (y : ℝ) (hy : 0 < y) :
    f y = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_whittaker_ode_neg_weight_eq_zero_of_moderateGrowth_of_mellin_eq_GammaC_mul.solution
