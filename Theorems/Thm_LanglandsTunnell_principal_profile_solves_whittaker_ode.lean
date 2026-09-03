import Definitions.Def_LanglandsTunnell_ArchParam
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_principal_profile_solves_whittaker_ode

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.principal_profile_solves_whittaker_ode (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ)
    (a₂ : ZMod 2) (ha₁ : a₁ = 0) (ha₂ : a₂ = 0) (c ν : ℂ) (hc : c = (u₁ + u₂) / 2)
    (hν : ν = (u₁ - u₂) / 2) (k : ℝ) (hk : k = 0) (f : ℝ → ℂ)
    (hf : ∀ y : ℝ, f y = (y : ℂ) ^ (1 / 2 - c) *
      ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (u₁ + signShift a₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (u₂ + signShift a₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ))) :
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_principal_profile_solves_whittaker_ode.solution
