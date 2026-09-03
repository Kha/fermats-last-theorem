import Mathlib
import P2M.Util
import P2M.Sol.S_Associated_of_pow_eq_units_mul_pow

set_option autoImplicit false

theorem Associated.of_pow_eq_units_mul_pow
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (a b : R) (n : ℕ) (hn : n ≠ 0) (u : Rˣ) (h : a ^ n = (u : R) * b ^ n) :
    Associated a b := by p2m_exact_reverting @_root_.P2MW.S_Associated_of_pow_eq_units_mul_pow.solution
