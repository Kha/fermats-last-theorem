import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_isDomain_of_isLocalizationAtPrime_of_prime_algebraMap

set_option autoImplicit false

open IsLocalRing

theorem Algebra.FormallySmooth.isDomain_of_isLocalizationAtPrime_of_prime_algebraMap
    {A B S : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [Algebra A B]
    [Algebra.FormallySmooth A B] [Algebra.FinitePresentation A B]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (hprime : Prime (algebraMap A B ϖ))
    (𝔫 : Ideal B) [𝔫.IsMaximal] (hϖ𝔫 : algebraMap A B ϖ ∈ 𝔫)
    [CommRing S] [Algebra B S] [IsLocalization.AtPrime S 𝔫] [IsLocalRing S] :
    IsDomain S := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_isDomain_of_isLocalizationAtPrime_of_prime_algebraMap.solution
