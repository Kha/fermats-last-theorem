import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv
    (n : ℕ) (σ : ℝ) :
    (Real.exp (-(Real.pi * σ ^ 2)) : ℂ) *
        ∫ z : ℝ, ((σ : ℂ) - Complex.I * (z : ℂ)) ^ n * (Real.exp (-(Real.pi * z ^ 2)) : ℂ) =
      (-(2 * (Real.pi : ℂ)))⁻¹ ^ n * iteratedDeriv n (fun s : ℝ => (Real.exp (-(Real.pi * s ^ 2)) : ℂ)) σ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv.solution
