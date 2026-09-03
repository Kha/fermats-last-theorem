import Mathlib
import P2M.Util
import P2M.Sol.S_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero

set_option autoImplicit false

theorem QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero
    (K : Type) [Field K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ x₀ x₁ x₂ x₃ : K, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 →
        x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ↔
      ∀ z x y : K, z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 → z = 0 ∧ x = 0 ∧ y = 0 := by p2m_exact_reverting @_root_.P2MW.S_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero.solution
