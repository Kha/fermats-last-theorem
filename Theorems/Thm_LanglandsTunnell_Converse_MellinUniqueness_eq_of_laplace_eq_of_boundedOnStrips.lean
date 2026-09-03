import Definitions.Def_LanglandsTunnell_HonestLDatum
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_MellinUniqueness_eq_of_laplace_eq_of_boundedOnStrips

set_option autoImplicit false
open MeasureTheory

theorem LanglandsTunnell.Converse.MellinUniqueness.eq_of_laplace_eq_of_boundedOnStrips
    (g₁ g₂ : ℝ → ℂ) (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (c : ℝ) (Λ : ℂ → ℂ) (hΛ : Differentiable ℂ Λ) (hb : LDatum.BoundedOnStrips Λ)
    (h₁ : ∀ s : ℂ, c < s.re →
      Integrable (fun t : ℝ => g₁ t * Complex.exp (s * (t : ℂ))) ∧ ∫ t : ℝ, g₁ t * Complex.exp (s * (t : ℂ)) = Λ s)
    (h₂ : ∀ s : ℂ, s.re < -c →
      Integrable (fun t : ℝ => g₂ t * Complex.exp (s * (t : ℂ))) ∧ ∫ t : ℝ, g₂ t * Complex.exp (s * (t : ℂ)) = Λ s) :
    g₁ = g₂ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_MellinUniqueness_eq_of_laplace_eq_of_boundedOnStrips.solution
