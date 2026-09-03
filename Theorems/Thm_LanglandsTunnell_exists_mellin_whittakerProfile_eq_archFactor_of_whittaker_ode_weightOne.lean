import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne (u₁ u₂ : ℂ)
    (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂) (W : ℂ → ℂ) (f : ℝ → ℂ) (c : ℂ)
    (hc : c = u₁ - u₂ ∨ c = u₂ - u₁)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv f) y
          + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 + 2 * (π : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N)
    (hne : ∃ y : ℝ, 0 < y ∧ f y ≠ 0)
    (hWp : ∀ t : ℝ, 0 < t → W t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * f t)
    (hWm : ∀ t : ℝ, 0 < t →
      c * W (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
        * (2 * (t : ℂ) * deriv f t + (4 * (π : ℂ) * (t : ℂ) - 1) * f t)) :
    ∃ P' : RealArchParam,
      (P' = RealArchParam.principal u₁ a₁ u₂ a₂ ∨ P' = RealArchParam.principal u₁ a₂ u₂ a₁) ∧
      ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (b : ZMod 2) (s : ℂ), max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (ρ * W t + (-1 : ℂ) ^ b.val * (ρ * W (-t))) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (ρ * W t + (-1 : ℂ) ^ b.val * (ρ * W (-t))) / (t : ℂ)) s
            = (P'.twist 0 b).archFactor s := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne.solution
