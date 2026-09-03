import Mathlib
import P2M.Util
import P2M.Sol.S_eq_one_of_isNilpotent_sub_one_of_pow_eq_one

set_option autoImplicit false

theorem eq_one_of_isNilpotent_sub_one_of_pow_eq_one
    {A : Type*} [Ring A] {u : A} (hu : IsNilpotent (u - 1))
    {m : ℕ} (hm : IsUnit (m : A)) (h : u ^ m = 1) :
    u = 1 := by p2m_exact_reverting @_root_.P2MW.S_eq_one_of_isNilpotent_sub_one_of_pow_eq_one.solution
