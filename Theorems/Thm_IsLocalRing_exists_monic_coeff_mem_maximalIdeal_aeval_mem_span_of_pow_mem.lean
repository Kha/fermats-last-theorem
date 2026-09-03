import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_monic_coeff_mem_maximalIdeal_aeval_mem_span_of_pow_mem

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsLocalRing.exists_monic_coeff_mem_maximalIdeal_aeval_mem_span_of_pow_mem
    {A S : Type*} [CommRing A] [IsLocalRing A] [CommRing S] [Algebra A S]
    (h T : S) [Module.Finite A (S ⧸ Ideal.span ({h} : Set S))]
    (hnil : ∃ k : ℕ, (Ideal.Quotient.mk (Ideal.span ({h} : Set S)) T) ^ k ∈
      (maximalIdeal A).map (algebraMap A (S ⧸ Ideal.span ({h} : Set S)))) :
    ∃ P : Polynomial A, P.Monic ∧ (∀ i : ℕ, i < P.natDegree → P.coeff i ∈ maximalIdeal A) ∧
      Polynomial.aeval T P ∈ Ideal.span ({h} : Set S) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_monic_coeff_mem_maximalIdeal_aeval_mem_span_of_pow_mem.solution
