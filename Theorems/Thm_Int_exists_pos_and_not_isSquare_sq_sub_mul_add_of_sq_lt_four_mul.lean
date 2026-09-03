import Mathlib
import P2M.Util
import P2M.Sol.S_Int_exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul

set_option autoImplicit false
theorem Int.exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul
    (t n : ℤ) (htn : t ^ 2 < 4 * n) :
    ∃ k : ℤ, 0 < k ^ 2 - t * k + n ∧ ¬ IsSquare (k ^ 2 - t * k + n) := by p2m_exact_reverting @_root_.P2MW.S_Int_exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul.solution
