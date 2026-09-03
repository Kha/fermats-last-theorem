import Definitions.Def_LanglandsTunnell_ArchBessel
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ArchBessel_besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div

set_option autoImplicit false

open MeasureTheory Set LanglandsTunnell.ArchBessel

theorem LanglandsTunnell.ArchBessel.besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div
    (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    besselKernel ν x =
      (((2 / x : ℝ)) : ℂ) ^ ν *
        ∫ τ in Set.Ioi (0 : ℝ), (Real.exp (-(τ + x ^ 2 / (4 * τ))) : ℂ) * ((τ : ℂ) ^ (ν - 1)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ArchBessel_besselKernel_eq_cpow_mul_integral_exp_neg_sub_sq_div.solution
