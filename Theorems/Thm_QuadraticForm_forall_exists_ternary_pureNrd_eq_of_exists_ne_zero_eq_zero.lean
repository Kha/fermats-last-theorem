import Mathlib
import P2M.Util
import P2M.Sol.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero

theorem QuadraticForm.forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero
    (F : Type) [Field F] [CharZero F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hiso : ∃ x y z : F, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = 0)
    (c : F) :
    ∃ x y z : F, -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = c := by p2m_exact_reverting @_root_.P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.solution
