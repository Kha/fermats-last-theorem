import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div

set_option autoImplicit false

theorem LanglandsTunnell.mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div
    (α β u s : ℂ) (k : ℕ) (hk : 1 ≤ k)
    (h₁ : 0 < (s + α + u + (k : ℂ) / 2).re) (h₂ : 0 < (s + β + u + (k : ℂ) / 2).re) :
    MellinConvergent (fun y : ℝ =>
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ α * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) *
        ((2 : ℂ) • ((y : ℂ) ^ (u + (k : ℂ) / 2) • ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ)))) s ∧
    mellin (fun y : ℝ =>
        ((4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          ((t : ℂ) ^ α * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
            (((y / t : ℝ) : ℂ) ^ β * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) *
        ((2 : ℂ) • ((y : ℂ) ^ (u + (k : ℂ) / 2) • ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ)))) s
      = 2 * (Complex.Gammaℂ (s + α + u + (k : ℂ) / 2) * Complex.Gammaℂ (s + β + u + (k : ℂ) / 2)) /
        Complex.Gammaℝ (2 * s + α + β + 2 * u + (k : ℂ) + 1) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_mellin_mulConvGaussian_mul_discreteProfile_eq_GammaC_mul_GammaC_div.solution
