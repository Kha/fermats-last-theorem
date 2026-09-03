import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import P2M.Util
import P2M.Sol.S_Complex_mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance

set_option autoImplicit false

open MeasureTheory Set

theorem Complex.mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance
    (A a b D : ℂ) (hA : 0 < A.re) (ha : 0 < a.re) (hD : 0 < D.re) (hba : 0 < (b - a).re)
    (hbA : 0 < (b - A + 1).re) (haD : 0 < (a + D - A + 1).re) :
    a * (∫ x in Set.Ioi (0:ℝ), ∫ y in Set.Ioi (0:ℝ),
        (x : ℂ) ^ (A - 1) * ((1 + x : ℝ) : ℂ) ^ (-(a + 1)) *
          ((y : ℂ) ^ (a + D - 1) * ((1 + y : ℝ) : ℂ) ^ (-b)) * ((1 + x + y : ℝ) : ℂ) ^ (-D)) +
    D * (∫ x in Set.Ioi (0:ℝ), ∫ y in Set.Ioi (0:ℝ),
        (x : ℂ) ^ (A - 1) * ((1 + x : ℝ) : ℂ) ^ (-a) *
          ((y : ℂ) ^ (a + D - 1) * ((1 + y : ℝ) : ℂ) ^ (-b)) * ((1 + x + y : ℝ) : ℂ) ^ (-(D + 1)))
      = Complex.Gamma A * Complex.Gamma (b - A + 1) * Complex.Gamma (a + D - A + 1) * Complex.Gamma (b - a) /
          (Complex.Gamma b * Complex.Gamma (D + b - A + 1)) := by p2m_exact_reverting @_root_.P2MW.S_Complex_mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance.solution
