import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_exists_not_mem_and_mul_mem_span_singleton_of_forall_mem_minimalPrimes_not_mem

set_option autoImplicit false

universe u

theorem IsIntegrallyClosed.exists_not_mem_and_mul_mem_span_singleton_of_forall_mem_minimalPrimes_not_mem
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (x : A) (𝔪 : Ideal A) [𝔪.IsPrime] (t : A)
    (ht : ∀ 𝔮 ∈ (Ideal.span {x}).minimalPrimes, 𝔮 ≤ 𝔪 → t ∉ 𝔮)
    (a : A) (ha : t * a ∈ Ideal.span {x}) :
    ∃ s : A, s ∉ 𝔪 ∧ s * a ∈ Ideal.span {x} := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_exists_not_mem_and_mul_mem_span_singleton_of_forall_mem_minimalPrimes_not_mem.solution
