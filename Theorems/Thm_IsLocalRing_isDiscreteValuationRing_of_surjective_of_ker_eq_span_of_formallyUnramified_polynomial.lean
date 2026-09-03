import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isDiscreteValuationRing_of_surjective_of_ker_eq_span_of_formallyUnramified_polynomial

set_option autoImplicit false

theorem IsLocalRing.isDiscreteValuationRing_of_surjective_of_ker_eq_span_of_formallyUnramified_polynomial
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    {S : Type} [CommRing S] [IsLocalRing S]
    (φ : Polynomial A →+* S) (hφu : φ.FormallyUnramified) (hφf : φ.EssFiniteType)
    (ht : φ Polynomial.X ∈ IsLocalRing.maximalIdeal S)
    {T : Type} [CommRing T] [IsDomain T]
    (π : S →+* T) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = Ideal.span {φ (Polynomial.C ϖ)})
    (ht0 : π (φ Polynomial.X) ≠ 0) :
    ∃ _ : IsDiscreteValuationRing T, IsLocalRing.maximalIdeal T = Ideal.span {π (φ Polynomial.X)} := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isDiscreteValuationRing_of_surjective_of_ker_eq_span_of_formallyUnramified_polynomial.solution
