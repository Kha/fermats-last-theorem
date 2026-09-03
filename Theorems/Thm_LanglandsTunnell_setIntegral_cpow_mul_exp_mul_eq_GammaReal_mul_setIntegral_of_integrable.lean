import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_setIntegral_cpow_mul_exp_mul_eq_GammaReal_mul_setIntegral_of_integrable

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.setIntegral_cpow_mul_exp_mul_eq_GammaReal_mul_setIntegral_of_integrable
    (w : ℂ) (hw : -1 < w.re) (K : ℝ → ℝ → ℝ → ℂ)
    (hK : Measurable fun p : ℝ × ℝ × ℝ => K p.1 p.2.1 p.2.2)
    (hInt : Integrable (fun p : ℝ × ℝ × ℝ × ℝ =>
        ((p.1 : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * (p.1 ^ 2 * (p.2.2.1 ^ 2)⁻¹))) : ℂ) * K p.2.1 p.2.2.1 p.2.2.2)
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))))))) :
    (∫ a₂ in Ioi (0 : ℝ), ∫ t in Iio (0 : ℝ), ∫ u : ℝ, ∫ Y in Ioi (0 : ℝ),
        ((a₂ : ℝ) : ℂ) ^ w * (Real.exp (-(Real.pi * (a₂ ^ 2 * (u ^ 2)⁻¹))) : ℂ) * K t u Y)
      = (1 / 2 : ℂ) * Complex.Gammaℝ (w + 1) *
        ∫ t in Iio (0 : ℝ), ∫ Y in Ioi (0 : ℝ), ∫ u : ℝ, ((|u| : ℝ) : ℂ) ^ (w + 1) * K t u Y := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_setIntegral_cpow_mul_exp_mul_eq_GammaReal_mul_setIntegral_of_integrable.solution
