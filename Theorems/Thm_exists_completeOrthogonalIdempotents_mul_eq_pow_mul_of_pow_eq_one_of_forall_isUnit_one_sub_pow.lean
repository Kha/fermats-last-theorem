import Mathlib
import P2M.Util
import P2M.Sol.S_exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow

set_option autoImplicit false

universe u

theorem exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow
    (R : Type u) [CommRing R] (N : ℕ) (hd : IsUnit ((N + 1 : ℕ) : R))
    (ζ : R) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : R) (hω : ω ^ (N + 1) = 1) :
    ∃ e : Fin (N + 1) → R, CompleteOrthogonalIdempotents e ∧ ∀ k : Fin (N + 1), ω * e k = ζ ^ (k : ℕ) * e k := by p2m_exact_reverting @_root_.P2MW.S_exists_completeOrthogonalIdempotents_mul_eq_pow_mul_of_pow_eq_one_of_forall_isUnit_one_sub_pow.solution
