import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_pow_mul_eq_of_mem_adjoin_div

set_option autoImplicit false

theorem Algebra.exists_pow_mul_eq_of_mem_adjoin_div
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (I : Ideal R) (a : R) (ha : a ∈ I) (x : S)
    (hx : x ∈ Algebra.adjoin R {x : S | ∃ i ∈ I, x * algebraMap R S a = algebraMap R S i}) :
    ∃ (n : ℕ) (c : R), c ∈ I ^ n ∧ x * algebraMap R S a ^ n = algebraMap R S c := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_pow_mul_eq_of_mem_adjoin_div.solution
