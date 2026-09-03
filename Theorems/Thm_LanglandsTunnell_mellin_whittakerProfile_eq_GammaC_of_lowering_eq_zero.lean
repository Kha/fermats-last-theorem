import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_mellin_whittakerProfile_eq_GammaC_of_lowering_eq_zero

set_option autoImplicit false

open scoped Real

theorem LanglandsTunnell.mellin_whittakerProfile_eq_GammaC_of_lowering_eq_zero (e : ℂ) (k₀ : ℤ) (W : ℂ → ℂ)
    (fp fm : ℝ → ℂ)
    (hWp : ∀ t : ℝ, 0 < t → W t = ((Real.sqrt t : ℝ) : ℂ) ^ (e + 1) * fp t)
    (hWm : ∀ t : ℝ, 0 < t → W (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (e + 1) * fm t)
    (hfp : DifferentiableOn ℝ fp (Set.Ioi 0)) (hfm : DifferentiableOn ℝ fm (Set.Ioi 0))
    (hlowp : ∀ y : ℝ, 0 < y →
      2 * (y : ℂ) * deriv fp y + (4 * (π : ℂ) * (y : ℂ) - (k₀ : ℂ)) * fp y = 0)
    (hlowm : ∀ y : ℝ, 0 < y →
      2 * (y : ℂ) * deriv fm y - (4 * (π : ℂ) * (y : ℂ) + (k₀ : ℂ)) * fm y = 0)
    (hgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖fm y‖ ≤ C * y ^ N)
    (hne : ∃ y : ℝ, 0 < y ∧ fp y ≠ 0) :
    (∀ t : ℝ, t < 0 → W t = 0) ∧
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (b : ZMod 2) (s : ℂ), -(e / 2 + ((k₀ : ℂ) - 1) / 2).re < s.re →
      MellinConvergent (fun t : ℝ => (ρ * W t + (-1 : ℂ) ^ b.val * (ρ * W (-t))) / (t : ℂ)) s ∧
        mellin (fun t : ℝ => (ρ * W t + (-1 : ℂ) ^ b.val * (ρ * W (-t))) / (t : ℂ)) s
          = Complex.Gammaℂ (s + (e / 2 + ((k₀ : ℂ) - 1) / 2)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_mellin_whittakerProfile_eq_GammaC_of_lowering_eq_zero.solution
