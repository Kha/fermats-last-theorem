import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous
    (m : ℕ) (a : ℂ) (ha : (m : ℝ) - 1 < a.re) (v : ℝ) (hv : 0 < v)
    (p : MvPolynomial (Fin 2) ℂ) (hp : p.IsHomogeneous m) :
    ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
        (((σ * w - v : ℝ) : ℂ) ^ a) * ((w : ℂ) ^ ((1 : ℤ) - (m : ℤ))) *
          (Real.exp (-(Real.pi * (σ ^ 2 + w ^ 2))) : ℂ) *
          (∫ z : ℝ, MvPolynomial.eval ![(σ : ℂ) - Complex.I * (z : ℂ), (w : ℂ)] p * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))
      = (1 / 2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-a - 1) * Complex.Gamma (a + 1) *
          (Real.exp (-(2 * Real.pi * v)) : ℂ) * MvPolynomial.eval ![(1 : ℂ), 1] p := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous.solution
