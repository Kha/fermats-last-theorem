import Mathlib
import P2M.Util
import P2M.Sol.S_Padic_exists_ternary_isotropic_two_mul_iff_of_norm_eq_one

theorem Padic.exists_ternary_isotropic_two_mul_iff_of_norm_eq_one (a b : ℚ_[2]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (∃ z x y : ℚ_[2], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (2 * a) * x ^ 2 - b * y ^ 2 = 0) ↔
      ‖b - 1‖ ≤ (2 : ℝ) ^ (-3 : ℤ) ∨ ‖2 * a + b - 1‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_Padic_exists_ternary_isotropic_two_mul_iff_of_norm_eq_one.solution
