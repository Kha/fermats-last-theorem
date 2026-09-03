import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import P2M.Util
import P2M.Sol.S_Complex_integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance

set_option autoImplicit false

open MeasureTheory Set

theorem Complex.integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance
    (A a b D : ℂ) (hA : 0 < A.re) (hbA : 0 < (b - A).re) (haD : 0 < (a + D - A).re) (hba : 0 < (b - a).re) :
    ∫ x in Set.Ioi (0:ℝ), ∫ y in Set.Ioi (0:ℝ),
        (x : ℂ) ^ (A - 1) * ((1 + x : ℝ) : ℂ) ^ (-a) *
          ((y : ℂ) ^ (a + D - 1) * ((1 + y : ℝ) : ℂ) ^ (-b)) * ((1 + x + y : ℝ) : ℂ) ^ (-D)
      = Complex.Gamma A * Complex.Gamma (b - A) * Complex.Gamma (a + D - A) * Complex.Gamma (b - a) /
          (Complex.Gamma b * Complex.Gamma (D + b - A)) := by p2m_exact_reverting @_root_.P2MW.S_Complex_integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance.solution
