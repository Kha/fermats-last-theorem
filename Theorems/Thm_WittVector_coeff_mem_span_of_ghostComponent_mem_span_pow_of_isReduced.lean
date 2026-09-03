import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_coeff_mem_span_of_ghostComponent_mem_span_pow_of_isReduced

set_option autoImplicit false

universe u

theorem WittVector.coeff_mem_span_of_ghostComponent_mem_span_pow_of_isReduced
    {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime] (hp : (p : S) ∈ nonZeroDivisors S)
    (hred : IsReduced (S ⧸ Ideal.span {(p : S)}))
    (z : WittVector p S) (N : ℕ)
    (hz : WittVector.ghostComponent (N - 1) z ∈ Ideal.span {(p : S) ^ N}) :
    ∀ j : ℕ, j < N → z.coeff j ∈ Ideal.span {(p : S)} := by p2m_exact_reverting @_root_.P2MW.S_WittVector_coeff_mem_span_of_ghostComponent_mem_span_pow_of_isReduced.solution
