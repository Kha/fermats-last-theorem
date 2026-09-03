import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_integral_ofReal_pow_three_mul_exp_neg_pi_mul_sq_div_sq_mul_psi

set_option autoImplicit false

p2m_open "LanglandsTunnell~integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv LanglandsTunnell.Converse MeasureTheory"

theorem LanglandsTunnell.Converse.integral_ofReal_pow_three_mul_exp_neg_pi_mul_sq_div_sq_mul_psi (c : ℝ) {Y : ℝ} (hY : Y ≠ 0) :
    ∫ x : ℝ, ((x : ℝ) : ℂ) ^ 3 * (Real.exp (-(Real.pi * (x ^ 2 / Y ^ 2))) : ℂ) * ArchR.psi (c * x) =
      ((|Y| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * Y ^ 2))) : ℂ) * (Complex.I * (((c * Y ^ 4 * (3 / (2 * Real.pi) - c ^ 2 * Y ^ 2)) : ℝ) : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_integral_ofReal_pow_three_mul_exp_neg_pi_mul_sq_div_sq_mul_psi.solution
