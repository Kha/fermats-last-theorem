import Mathlib
import P2M.Util
import P2M.Sol.S_QuadraticForm_exists_ternary_isotropic_mul_of_exists_of_exists

set_option autoImplicit false

theorem QuadraticForm.exists_ternary_isotropic_mul_of_exists_of_exists
    (K : Type) [Field K] (t u u' : K)
    (h : ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - t * x ^ 2 - u * y ^ 2 = 0)
    (h' : ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - t * x ^ 2 - u' * y ^ 2 = 0) :
    ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - t * x ^ 2 - (u * u') * y ^ 2 = 0 := by p2m_exact_reverting @_root_.P2MW.S_QuadraticForm_exists_ternary_isotropic_mul_of_exists_of_exists.solution
