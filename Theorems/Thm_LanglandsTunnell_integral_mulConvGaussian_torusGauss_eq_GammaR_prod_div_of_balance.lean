import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance
    (p₁ p₂ q₁ q₂ α β γ : ℂ)
    (hbal : β - γ = 2 * α + 2 + p₁ + p₂)
    (hp₁ : 0 < (α - β + p₁).re) (hp₂ : 0 < (α - β + p₂).re)
    (h₁₁ : 0 < (α + 1 + p₁ + q₁).re) (h₁₂ : 0 < (α + 1 + p₁ + q₂).re)
    (h₂₁ : 0 < (α + 1 + p₂ + q₁).re) (h₂₂ : 0 < (α + 1 + p₂ + q₂).re) :
    (∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ p₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ p₂ * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ α *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ q₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * y₁ / y₂) / r : ℝ) : ℂ) ^ q₂ * (Real.exp (-(Real.pi * ((t * y₁ / y₂) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ))
      = (1 / 2 : ℂ) *
          (Complex.Gammaℝ (α - β + p₁) * Complex.Gammaℝ (α - β + p₂) *
            (Complex.Gammaℝ (α + 1 + p₁ + q₁) * Complex.Gammaℝ (α + 1 + p₁ + q₂) *
              Complex.Gammaℝ (α + 1 + p₂ + q₁) * Complex.Gammaℝ (α + 1 + p₂ + q₂))) /
          Complex.Gammaℝ (β - γ + q₁ + q₂) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance.solution
