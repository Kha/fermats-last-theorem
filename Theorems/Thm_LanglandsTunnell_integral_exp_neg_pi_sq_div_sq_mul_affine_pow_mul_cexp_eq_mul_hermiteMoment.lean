import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_integral_exp_neg_pi_sq_div_sq_mul_affine_pow_mul_cexp_eq_mul_hermiteMoment

set_option autoImplicit false

open MeasureTheory Complex FourierTransform

theorem LanglandsTunnell.integral_exp_neg_pi_sq_div_sq_mul_affine_pow_mul_cexp_eq_mul_hermiteMoment
    (α c : ℝ) {y₁ : ℝ} (hy₁ : y₁ ≠ 0) (m : ℕ) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
        (((α : ℝ) : ℂ) + (Complex.I * (((1 / y₁ : ℝ)) : ℂ)) * (x : ℂ)) ^ m *
        Complex.exp (2 * Real.pi * Complex.I * (c : ℂ) * (x : ℂ)) =
      ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) *
        ∫ u : ℝ, (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * ((((α - c * y₁ : ℝ)) : ℂ) + Complex.I * (u : ℂ)) ^ m := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_integral_exp_neg_pi_sq_div_sq_mul_affine_pow_mul_cexp_eq_mul_hermiteMoment.solution
