import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_tsum_one_div_add_int_pow_three

set_option autoImplicit false

open scoped Real
open Complex

theorem Complex.tsum_one_div_add_int_pow_three (x : ℝ) (hx : ∀ n : ℤ, (x : ℝ) ≠ n) :
    ∑' n : ℤ, 1 / ((x : ℂ) + n) ^ 3 =
      -((2 * π * I) ^ 3 / 2) *
        (Complex.exp (2 * π * I * x) * (1 + Complex.exp (2 * π * I * x)) / (1 - Complex.exp (2 * π * I * x)) ^ 3) := by p2m_exact_reverting @_root_.P2MW.S_Complex_tsum_one_div_add_int_pow_three.solution
