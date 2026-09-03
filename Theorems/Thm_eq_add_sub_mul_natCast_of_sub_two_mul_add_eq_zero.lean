import Mathlib
import P2M.Util
import P2M.Sol.S_eq_add_sub_mul_natCast_of_sub_two_mul_add_eq_zero

set_option autoImplicit false

theorem eq_add_sub_mul_natCast_of_sub_two_mul_add_eq_zero
    {R : Type*} [CommRing R] (e : ℕ) (a : ℕ → R)
    (h : ∀ k : ℕ, k + 1 < e → a k - 2 * a (k + 1) + a (k + 2) = 0)
    (k : ℕ) (hk : k ≤ e) :
    a k = a 0 + (a 1 - a 0) * k := by p2m_exact_reverting @_root_.P2MW.S_eq_add_sub_mul_natCast_of_sub_two_mul_add_eq_zero.solution
