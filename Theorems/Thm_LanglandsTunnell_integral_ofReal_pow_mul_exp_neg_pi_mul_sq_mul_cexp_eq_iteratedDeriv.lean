import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv

set_option autoImplicit false

open MeasureTheory Complex FourierTransform

theorem LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv (j : ℕ) (ξ : ℝ) :
    ∫ x : ℝ, ((x : ℝ) : ℂ) ^ j * (Real.exp (-(Real.pi * x ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ)) =
      (2 * Real.pi * Complex.I)⁻¹ ^ j * iteratedDeriv j (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) ξ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv.solution
