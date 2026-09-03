import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_exists_etaleCoordinate_of_krullDimLE_one

set_option autoImplicit false

open IsLocalRing

theorem Algebra.FormallySmooth.exists_etaleCoordinate_of_krullDimLE_one
    {A B S : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [Algebra A B]
    [Algebra.FormallySmooth A B] [Algebra.FinitePresentation A B]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (hprime : Prime (algebraMap A B ϖ)) (hdim : Ring.KrullDimLE 1 (B ⧸ Ideal.span {algebraMap A B ϖ}))
    (𝔫 : Ideal B) [𝔫.IsMaximal] (hϖ𝔫 : algebraMap A B ϖ ∈ 𝔫) (hne : 𝔫 ≠ Ideal.span {algebraMap A B ϖ})
    (hrat : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap A B)))
    [CommRing S] [Algebra B S] [IsLocalization.AtPrime S 𝔫] [IsLocalRing S] :
    ∃ t : B, t ∈ 𝔫 ∧
      maximalIdeal S = Ideal.span {algebraMap B S (algebraMap A B ϖ), algebraMap B S t} ∧
      (Polynomial.eval₂RingHom ((algebraMap B S).comp (algebraMap A B)) (algebraMap B S t)).FormallySmooth ∧
      (Polynomial.eval₂RingHom ((algebraMap B S).comp (algebraMap A B)) (algebraMap B S t)).FormallyUnramified ∧
      (Polynomial.eval₂RingHom ((algebraMap B S).comp (algebraMap A B)) (algebraMap B S t)).EssFiniteType := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_exists_etaleCoordinate_of_krullDimLE_one.solution
