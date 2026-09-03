import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime

universe u

theorem Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
    (P : Type u) [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    (A : Type u) [CommRing A] [Algebra P A] [Algebra.Etale P A]
    (q : Ideal A) [q.IsPrime] (A_q : Type u) [CommRing A_q] [Algebra A A_q] [IsLocalization.AtPrime A_q q] :
    IsDomain A_q ∧ IsIntegrallyClosed A_q := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.solution
