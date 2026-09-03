import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightZero

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightZero (u₁ u₂ : ℂ)
    (a : ZMod 2) (W₀ W₂ : ℂ → ℂ) (f₀ : ℝ → ℂ)
    (hf₀ : DifferentiableOn ℝ f₀ (Set.Ioi 0)) (hf₀' : DifferentiableOn ℝ (deriv f₀) (Set.Ioi 0))
    (hode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv f₀) y
          + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f₀ y = 0)
    (hgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f₀ y‖ ≤ C * y ^ N)
    (hne : ∃ y : ℝ, 0 < y ∧ f₀ y ≠ 0)
    (hW0p : ∀ t : ℝ, 0 < t → W₀ t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * f₀ t)
    (hW0m : ∀ t : ℝ, 0 < t →
      W₀ (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * ((-1 : ℂ) ^ a.val * f₀ t))
    (hW2p : ∀ t : ℝ, 0 < t →
      W₂ t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
        * (-(1 / (4 * (π : ℂ))) * (2 * (t : ℂ) * deriv f₀ t - 4 * (π : ℂ) * (t : ℂ) * f₀ t)))
    (hW2m : ∀ t : ℝ, 0 < t →
      W₂ (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
        * (-(1 / (4 * (π : ℂ))) * ((-1 : ℂ) ^ a.val * (2 * (t : ℂ) * deriv f₀ t + 4 * (π : ℂ) * (t : ℂ) * f₀ t)))) :
    ∃ ρ : ℂ, ρ ≠ 0 ∧
      (∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (ρ * W₀ t + (-1 : ℂ) ^ a.val * (ρ * W₀ (-t))) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (ρ * W₀ t + (-1 : ℂ) ^ a.val * (ρ * W₀ (-t))) / (t : ℂ)) s
            = ((RealArchParam.principal u₁ a u₂ a).twist 0 a).archFactor s) ∧
      (∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ a.val * (ρ * W₂ (-t))) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ a.val * (ρ * W₂ (-t))) / (t : ℂ)) s
            = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
                * ((RealArchParam.principal u₁ a u₂ a).twist 0 a).archFactor s) ∧
      (∀ s : ℂ, max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ (a + 1).val * (ρ * W₂ (-t))) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (ρ * W₂ t + (-1 : ℂ) ^ (a + 1).val * (ρ * W₂ (-t))) / (t : ℂ)) s
            = ((RealArchParam.principal u₁ a u₂ a).twist 0 (a + 1)).archFactor s) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightZero.solution
