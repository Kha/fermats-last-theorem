import Mathlib
import P2M.Util
import P2M.Sol.S_pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728
set_option autoImplicit false

theorem pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728
    {k : Type*} [Field k] {q : ℕ} [Fact q.Prime] [CharP k q] (hq : 5 ≤ q)
    (a : k) (h01728 : a = 0 ∨ a = 1728) (l : k)
    (hl : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3) :
    l ^ (q ^ 2) = l := by p2m_exact_reverting @_root_.P2MW.S_pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728.solution
