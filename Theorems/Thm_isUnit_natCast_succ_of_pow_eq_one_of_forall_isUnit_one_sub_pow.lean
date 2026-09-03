import Mathlib
import P2M.Util
import P2M.Sol.S_isUnit_natCast_succ_of_pow_eq_one_of_forall_isUnit_one_sub_pow

set_option autoImplicit false

universe u

theorem isUnit_natCast_succ_of_pow_eq_one_of_forall_isUnit_one_sub_pow
    (R : Type u) [CommRing R] (N : ℕ) (ζ : R) (hζ : ζ ^ (N + 1) = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j)) :
    IsUnit ((N + 1 : ℕ) : R) := by p2m_exact_reverting @_root_.P2MW.S_isUnit_natCast_succ_of_pow_eq_one_of_forall_isUnit_one_sub_pow.solution
