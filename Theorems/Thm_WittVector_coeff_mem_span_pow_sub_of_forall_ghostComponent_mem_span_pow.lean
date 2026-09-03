import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_coeff_mem_span_pow_sub_of_forall_ghostComponent_mem_span_pow

set_option autoImplicit false

universe u

theorem WittVector.coeff_mem_span_pow_sub_of_forall_ghostComponent_mem_span_pow
    {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime] (hp : (p : S) ∈ nonZeroDivisors S)
    (z : WittVector p S) (s M : ℕ)
    (hz : ∀ n : ℕ, n < M → WittVector.ghostComponent n z ∈ Ideal.span {(p : S) ^ s}) :
    ∀ j : ℕ, j < M → z.coeff j ∈ Ideal.span {(p : S) ^ (s - j)} := by p2m_exact_reverting @_root_.P2MW.S_WittVector_coeff_mem_span_pow_sub_of_forall_ghostComponent_mem_span_pow.solution
