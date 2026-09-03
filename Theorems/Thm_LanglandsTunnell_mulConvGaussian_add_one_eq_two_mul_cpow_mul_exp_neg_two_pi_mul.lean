import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_mulConvGaussian_add_one_eq_two_mul_cpow_mul_exp_neg_two_pi_mul

set_option autoImplicit false

theorem LanglandsTunnell.mulConvGaussian_add_one_eq_two_mul_cpow_mul_exp_neg_two_pi_mul
    (γ : ℂ) (y : ℝ) (hy : 0 < y) :
    (4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ γ * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) *
          (((y / t : ℝ) : ℂ) ^ (γ + 1) * (Real.exp (-(Real.pi * (y / t) ^ 2)) : ℂ)) / (t : ℂ)
      = 2 * ((y : ℂ) ^ γ * (Real.exp (-(2 * Real.pi * y)) : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_mulConvGaussian_add_one_eq_two_mul_cpow_mul_exp_neg_two_pi_mul.solution
