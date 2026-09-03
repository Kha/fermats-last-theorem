import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_integral_Ioi_cpow_mul_iteratedDeriv_exp_neg_pi_mul_sq_eq_prod_mul_integral_cpow_sub_mul_exp

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integral_Ioi_cpow_mul_iteratedDeriv_exp_neg_pi_mul_sq_eq_prod_mul_integral_cpow_sub_mul_exp
    (n : ℕ) (a : ℂ) (ha : (n : ℝ) - 1 < a.re) (w : ℝ) (hw : 0 < w) (v : ℝ) :
    ∫ σ in Ioi (v / w), (((σ * w - v : ℝ) : ℂ) ^ a) *
        iteratedDeriv n (fun s : ℝ => (Real.exp (-(Real.pi * s ^ 2)) : ℂ)) σ
      = (-(w : ℂ)) ^ n * (∏ k ∈ Finset.range n, (a - (k : ℂ))) *
          ∫ σ in Ioi (v / w), (((σ * w - v : ℝ) : ℂ) ^ (a - (n : ℂ))) *
            (Real.exp (-(Real.pi * σ ^ 2)) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_integral_Ioi_cpow_mul_iteratedDeriv_exp_neg_pi_mul_sq_eq_prod_mul_integral_cpow_sub_mul_exp.solution
