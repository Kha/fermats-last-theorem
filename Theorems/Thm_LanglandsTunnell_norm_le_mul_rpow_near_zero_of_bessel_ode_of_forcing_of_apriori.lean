import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori
    (ν : ℂ) (hν : 0 ≤ ν.re) (σ A r B : ℝ) (f h : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hh : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖h y‖ ≤ A * y ^ σ)
    (hapriori : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ B * y ^ r)
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = h y) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖(y : ℂ) * deriv f y - (1 / 2 - ν) * f y‖ ≤ C * y ^ (min (min (1 / 2 + ν.re) σ) (r + 2) - ε)) ∧
    (1 / 2 - ν.re < r → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖f y‖ ≤ C * y ^ (min (1 / 2 + ν.re) σ - ε) ∧
      ‖(y : ℂ) * deriv f y‖ ≤ C * y ^ (min (1 / 2 + ν.re) σ - ε)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori.solution
