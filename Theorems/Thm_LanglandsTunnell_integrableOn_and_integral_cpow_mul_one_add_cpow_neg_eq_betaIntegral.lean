import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_integrableOn_and_integral_cpow_mul_one_add_cpow_neg_eq_betaIntegral

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.integrableOn_and_integral_cpow_mul_one_add_cpow_neg_eq_betaIntegral
    (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (fun q : ℝ => (q : ℂ) ^ (b - 1) * ((1 + q : ℝ) : ℂ) ^ (-(a + b))) (Set.Ioi (0 : ℝ)) ∧
      ∫ q in Set.Ioi (0 : ℝ), (q : ℂ) ^ (b - 1) * ((1 + q : ℝ) : ℂ) ^ (-(a + b)) = Complex.betaIntegral b a := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_integrableOn_and_integral_cpow_mul_one_add_cpow_neg_eq_betaIntegral.solution
