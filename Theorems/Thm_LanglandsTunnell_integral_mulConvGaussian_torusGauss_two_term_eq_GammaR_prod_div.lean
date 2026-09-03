import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div
    (π₁ π₂ q₁ q₂ α β γ : ℂ)
    (hbal : β - γ = 2 * α + 2 + π₁ + π₂)
    (hp₁ : 0 < (α - β + π₁ + 1).re) (hp₂ : 0 < (α - β + π₂).re)
    (h₁₁ : 0 < (α + 1 + π₁ + q₁).re) (h₁₂ : 0 < (α + 1 + π₁ + q₂).re)
    (h₂₁ : 0 < (α + 2 + π₂ + q₁).re) (h₂₂ : 0 < (α + 2 + π₂ + q₂).re) :
    (∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (π₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (π₂ + 1) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (α) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (q₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * y₁ / y₂) / r : ℝ) : ℂ) ^ (q₂) * (Real.exp (-(Real.pi * ((t * y₁ / y₂) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ (β - 1) * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ)) +
    (∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (π₁ + 1) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (π₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (α + 1) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (q₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * y₁ / y₂) / r : ℝ) : ℂ) ^ (q₂) * (Real.exp (-(Real.pi * ((t * y₁ / y₂) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ (β + 1) * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ))
      = (1 / 2 : ℂ) *
          (Complex.Gammaℝ (α - β + π₁ + 1) * Complex.Gammaℝ (α - β + π₂) *
            (Complex.Gammaℝ (α + 1 + π₁ + q₁) * Complex.Gammaℝ (α + 1 + π₁ + q₂) *
              Complex.Gammaℝ (α + 2 + π₂ + q₁) * Complex.Gammaℝ (α + 2 + π₂ + q₂))) /
          Complex.Gammaℝ (β - γ + q₁ + q₂ + 1) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_integral_mulConvGaussian_torusGauss_two_term_eq_GammaR_prod_div.solution
