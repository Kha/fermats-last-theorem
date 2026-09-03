import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_discrete_profile_solves_whittaker_ode

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.discrete_profile_solves_whittaker_ode (n : ℕ) (k : ℝ) (ν : ℂ) (hk : k = n + 1)
    (hν : ν = (n : ℂ) / 2) (f : ℝ → ℂ)
    (hf : ∀ y : ℝ, f y = ((y ^ (1 / 2 : ℝ) * (2 * y ^ ((n : ℝ) / 2) * Real.exp (-(2 * π * y))) : ℝ) : ℂ)) :
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_discrete_profile_solves_whittaker_ode.solution
