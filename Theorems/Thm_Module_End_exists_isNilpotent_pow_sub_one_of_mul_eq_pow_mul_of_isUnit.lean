import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul_of_isUnit

set_option autoImplicit false

theorem Module.End.exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul_of_isUnit
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (g h : Module.End F V) (hg : IsUnit g) (hh : IsUnit h) {q : ℕ} (hq : 2 ≤ q)
    (hrel : h * g = g ^ q * h) :
    ∃ e : ℕ, 0 < e ∧ IsNilpotent (g ^ e - 1) := by p2m_exact_reverting @_root_.P2MW.S_Module_End_exists_isNilpotent_pow_sub_one_of_mul_eq_pow_mul_of_isUnit.solution
