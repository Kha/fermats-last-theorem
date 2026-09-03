import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import P2M.Util
import P2M.Sol.S_MeasureTheory_setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free
    (F : ℝ × ℝ × ℝ × ℝ → ℂ) (G : ℝ → ℝ → ℝ → ℂ)
    (hFG : ∀ x y₁ y₂ θ : ℝ, y₁ ≠ 0 → 0 < y₂ → F (x, y₁, y₂, θ) = G x y₁ y₂)
    (hG : Integrable (fun q : ℝ × ℝ × ℝ => G q.1 q.2.1 q.2.2)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) :
    ∫ p : ℝ × ℝ × ℝ × ℝ in Set.univ ×ˢ (Set.univ ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi))), F p =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ x : ℝ, G x y₁ y₂ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free.solution
