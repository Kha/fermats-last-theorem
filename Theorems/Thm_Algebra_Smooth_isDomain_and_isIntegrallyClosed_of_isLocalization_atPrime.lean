import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime

set_option autoImplicit false

universe u

theorem Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] (Sₚ : Type u) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization.AtPrime Sₚ p] :
    IsDomain Sₚ ∧ IsIntegrallyClosed Sₚ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.solution
