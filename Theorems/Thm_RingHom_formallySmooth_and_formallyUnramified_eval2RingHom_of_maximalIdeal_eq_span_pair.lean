import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_maximalIdeal_eq_span_pair

set_option autoImplicit false

open IsLocalRing

theorem RingHom.formallySmooth_and_formallyUnramified_eval2RingHom_of_maximalIdeal_eq_span_pair
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    {S : Type} [CommRing S] [IsDomain S] [IsLocalRing S]
    (i : A →+* S) (hi : i.FormallySmooth) (hif : i.EssFiniteType)
    (hres : Function.Surjective ((IsLocalRing.residue S).comp i))
    (t : S) (hm : maximalIdeal S = Ideal.span {i ϖ, t}) (ht : t ∉ Ideal.span {i ϖ}) :
    (Polynomial.eval₂RingHom i t).FormallySmooth ∧ (Polynomial.eval₂RingHom i t).FormallyUnramified ∧
      (Polynomial.eval₂RingHom i t).EssFiniteType := by p2m_exact_reverting @_root_.P2MW.S_RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_maximalIdeal_eq_span_pair.solution
