import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_integrableOn_and_integral_Ioi_exp_neg_pi_mul_sq_add_sq_div_sq_eq_half_exp

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integrableOn_and_integral_Ioi_exp_neg_pi_mul_sq_add_sq_div_sq_eq_half_exp
    (ρ : ℝ) (hρ : 0 < ρ) :
    IntegrableOn (fun w : ℝ => Real.exp (-(Real.pi * (w ^ 2 + ρ ^ 2 / w ^ 2)))) (Ioi 0) ∧
      ∫ w in Ioi (0 : ℝ), Real.exp (-(Real.pi * (w ^ 2 + ρ ^ 2 / w ^ 2))) =
        (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * ρ)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_integrableOn_and_integral_Ioi_exp_neg_pi_mul_sq_add_sq_div_sq_eq_half_exp.solution
