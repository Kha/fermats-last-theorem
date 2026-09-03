import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_moduleFinite_quotient_span_and_exists_pow_mem_of_isLocalizationAtPrime_of_mem_nonZeroDivisors

set_option autoImplicit false

open IsLocalRing

theorem HenselianLocalRing.moduleFinite_quotient_span_and_exists_pow_mem_of_isLocalizationAtPrime_of_mem_nonZeroDivisors
    {A : Type*} [CommRing A] [IsDomain A] [ValuationRing A] [HenselianLocalRing A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    (𝔫 : Ideal B) [𝔫.IsPrime] (h𝔫 : 𝔫.comap (algebraMap A B) = maximalIdeal A)
    {S : Type*} [CommRing S] [Algebra A S] [Algebra B S] [IsScalarTower A B S]
    [IsLocalization.AtPrime S 𝔫] [Module.Flat A S]
    (h T : S) (hT : ¬IsUnit T)
    (hreg : Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A S)) h ∈
      nonZeroDivisors (S ⧸ (maximalIdeal A).map (algebraMap A S)))
    (hfin : Module.Finite A (S ⧸ (Ideal.span ({h} : Set S) ⊔ (maximalIdeal A).map (algebraMap A S)))) :
    Module.Finite A (S ⧸ Ideal.span ({h} : Set S)) ∧
      ∃ k : ℕ, (Ideal.Quotient.mk (Ideal.span ({h} : Set S)) T) ^ k ∈
        (maximalIdeal A).map (algebraMap A (S ⧸ Ideal.span ({h} : Set S))) := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_moduleFinite_quotient_span_and_exists_pow_mem_of_isLocalizationAtPrime_of_mem_nonZeroDivisors.solution
