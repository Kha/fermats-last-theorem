import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_setIntegral_integral_dite_eq_const_mul_GammaR_mul_integral_triple_of_fibre

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.Converse.setIntegral_integral_dite_eq_const_mul_GammaR_mul_integral_triple_of_fibre
    (w : ℂ) (hw : -1 < w.re) (C : ℂ) (T T' : ℝ → ℝ → ℝ → ℂ)
    (hF : Integrable (fun r : ℝ × ℝ × ℝ × ℝ =>
        (((r.1 : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * r.1 ^ 2 * r.2.2.1 ^ 2)) : ℂ)) * T r.2.1 r.2.2.1 r.2.2.2)
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))))
    (hT' : ∀ t q p : ℝ, q ≠ 0 → 0 < p → T' t q p = ((|q| : ℝ) : ℂ) ^ (-w - 1) * T t q p)
    (Φ : ℝ → ℝ → ℂ)
    (hΦ : ∀ a₁ a₂ : ℝ, a₁ ≠ 0 → 0 < a₂ →
      Φ a₁ a₂ = C * (((a₂⁻¹ : ℝ)) : ℂ) *
        ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (((a₂ : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) : ℂ)) * T (a₁ / a₂) q p) :
    (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ, if ha : a₁ ≠ 0 ∧ 0 < a₂ then Φ a₁ a₂ else 0)
      = C * ((1 / 2 : ℂ) * Complex.Gammaℝ (w + 1)) *
        ∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ), T' t q p := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_setIntegral_integral_dite_eq_const_mul_GammaR_mul_integral_triple_of_fibre.solution
