import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_tsum_one_div_add_int_pow_four

set_option autoImplicit false

open scoped Real
open Complex

theorem Complex.tsum_one_div_add_int_pow_four (x : ℝ) (hx : ∀ n : ℤ, (x : ℝ) ≠ n) :
    ∑' n : ℤ, 1 / ((x : ℂ) + n) ^ 4 =
      (2 * π * I) ^ 4 / 6 *
        (Complex.exp (2 * π * I * x) * (Complex.exp (2 * π * I * x) ^ 2 + 4 * Complex.exp (2 * π * I * x) + 1) /
          (1 - Complex.exp (2 * π * I * x)) ^ 4) := by p2m_exact_reverting @_root_.P2MW.S_Complex_tsum_one_div_add_int_pow_four.solution
