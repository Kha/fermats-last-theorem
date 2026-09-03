import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_ideal_finite_quotient_forall_mem_span_singleton_of_mem_maximalIdeal

set_option autoImplicit false
theorem IsLocalRing.exists_ideal_finite_quotient_forall_mem_span_singleton_of_mem_maximalIdeal
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Finite (IsLocalRing.ResidueField A)]
    {ι : Type} (f : ι → A) (hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal A) (hf0 : ∃ i, f i ≠ 0) :
    ∃ (I : Ideal A) (t : A ⧸ I), I ≤ IsLocalRing.maximalIdeal A ∧ Finite (A ⧸ I) ∧ t ≠ 0 ∧
      (∃ a ∈ IsLocalRing.maximalIdeal A, Ideal.Quotient.mk I a = t) ∧
      (∀ m ∈ IsLocalRing.maximalIdeal A, t * Ideal.Quotient.mk I m = 0) ∧
      (∀ i, Ideal.Quotient.mk I (f i) ∈ Ideal.span {t}) ∧
      (∃ i, Ideal.Quotient.mk I (f i) ≠ 0) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_ideal_finite_quotient_forall_mem_span_singleton_of_mem_maximalIdeal.solution
