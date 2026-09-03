import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_map_comap_eq_of_minimalPrimes_span_of_ringEquiv_adicCompletion
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.map_comap_eq_of_minimalPrimes_span_of_ringEquiv_adicCompletion
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (S : Type) [CommRing S] [IsNoetherianRing S]
    (e : AdicCompletion (maximalIdeal R) R ≃+* S)
    (r : R) (π : S) (hπ : e (algebraMap R (AdicCompletion (maximalIdeal R) R) r) = π)
    (hrad : (Ideal.span {π}).IsRadical)
    (P : Ideal S) (hP : P ∈ (Ideal.span {π}).minimalPrimes)
    (huniq : ∀ P' ∈ (Ideal.span {π}).minimalPrimes,
      P'.comap ((e : AdicCompletion (maximalIdeal R) R →+* S).comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) =
        P.comap ((e : AdicCompletion (maximalIdeal R) R →+* S).comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) →
      P' = P) :
    (P.comap ((e : AdicCompletion (maximalIdeal R) R →+* S).comp (algebraMap R (AdicCompletion (maximalIdeal R) R)))).map
      ((e : AdicCompletion (maximalIdeal R) R →+* S).comp (algebraMap R (AdicCompletion (maximalIdeal R) R))) = P := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_map_comap_eq_of_minimalPrimes_span_of_ringEquiv_adicCompletion.solution
