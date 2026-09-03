import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallyUnramified_isRegularLocalRing_quotient_span_of_ringKrullDim_quotient_eq_one

set_option autoImplicit false

universe u

theorem Algebra.FormallyUnramified.isRegularLocalRing_quotient_span_of_ringKrullDim_quotient_eq_one
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    (ϖ : R) (hR : IsRegularLocalRing (R ⧸ Ideal.span {ϖ})) (hR1 : ringKrullDim (R ⧸ Ideal.span {ϖ}) = 1)
    (hS1 : ringKrullDim (S ⧸ Ideal.span {algebraMap R S ϖ}) = 1) :
    IsRegularLocalRing (S ⧸ Ideal.span {algebraMap R S ϖ}) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallyUnramified_isRegularLocalRing_quotient_span_of_ringKrullDim_quotient_eq_one.solution
