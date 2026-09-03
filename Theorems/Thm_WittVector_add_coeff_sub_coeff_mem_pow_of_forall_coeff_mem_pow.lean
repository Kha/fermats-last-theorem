import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow

universe u

theorem WittVector.add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow
    (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R] (I : Ideal R) (c : ℕ)
    (x y : WittVector p R) (hx : ∀ i : ℕ, x.coeff i ∈ I) (hy : ∀ i : ℕ, y.coeff i ∈ I ^ (p ^ i + c))
    (n : ℕ) :
    (x + y).coeff n - x.coeff n ∈ I ^ ((p - 1) * n + 1 + c) := by p2m_exact_reverting @_root_.P2MW.S_WittVector_add_coeff_sub_coeff_mem_pow_of_forall_coeff_mem_pow.solution
