import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Prod
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion
    (a : ℂ) (ha : -1 < a.re) (k : ℤ) (n : ℕ) (v : ℝ) (hv : 0 < v) :
    IntegrableOn (fun q : ℝ × ℝ =>
        ((q.1 * q.2 - v : ℝ) : ℂ) ^ a * (q.2 : ℂ) ^ k *
          (Real.exp (-(Real.pi * (q.1 ^ 2 + q.2 ^ 2))) : ℂ) *
          ∫ z : ℝ, ((q.1 : ℂ) - Complex.I * (z : ℂ)) ^ n * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))
      {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2} := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion.solution
