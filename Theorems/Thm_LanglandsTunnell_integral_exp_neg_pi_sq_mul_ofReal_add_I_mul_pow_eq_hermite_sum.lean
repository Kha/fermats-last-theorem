import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.MellinTransform
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_integral_exp_neg_pi_sq_mul_ofReal_add_I_mul_pow_eq_hermite_sum

set_option autoImplicit false

open MeasureTheory Complex

theorem LanglandsTunnell.integral_exp_neg_pi_sq_mul_ofReal_add_I_mul_pow_eq_hermite_sum (t : ℝ) (m : ℕ) :
    ∫ u : ℝ, (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * (((t : ℝ) : ℂ) + Complex.I * (u : ℂ)) ^ m =
      ∑ r ∈ Finset.range (m / 2 + 1),
          (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * ((m - 2 * r).factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) *
            ((t : ℝ) : ℂ) ^ (m - 2 * r) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_integral_exp_neg_pi_sq_mul_ofReal_add_I_mul_pow_eq_hermite_sum.solution
