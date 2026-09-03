import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_setIntegral_mulConvGaussian_mul_cpow_mul_exp_eq_betaIntegral_mul_GammaR

set_option autoImplicit false

open MeasureTheory Set
open scoped Real

theorem LanglandsTunnell.setIntegral_mulConvGaussian_mul_cpow_mul_exp_eq_betaIntegral_mul_GammaR
    (p q z : ℂ) (hp : 0 < (z + p).re) (hq : 0 < (z + q).re) :
    ∫ y in Ioi (0 : ℝ),
        ((4 : ℂ) * ∫ t in Ioi (0 : ℝ),
            ((t : ℂ) ^ p * (Real.exp (-(π * t ^ 2)) : ℂ)) *
              (((y / t : ℝ) : ℂ) ^ q * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)) *
          (y : ℂ) ^ (z - 1) * (Real.exp (-(2 * π * y)) : ℂ)
      = 2 * Complex.betaIntegral (z + p) (z + q) * Complex.Gammaℝ (2 * z + p + q) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_setIntegral_mulConvGaussian_mul_cpow_mul_exp_eq_betaIntegral_mul_GammaR.solution
