import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegral_of_forall_isPrime_isIntegral_quotient_mk

set_option autoImplicit false

universe u v

theorem IsIntegral.of_forall_isPrime_isIntegral_quotient_mk
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A] (a : A)
    (h : ∀ (p : Ideal A), p.IsPrime → IsIntegral R (Ideal.Quotient.mk p a)) :
    IsIntegral R a := by p2m_exact_reverting @_root_.P2MW.S_IsIntegral_of_forall_isPrime_isIntegral_quotient_mk.solution
