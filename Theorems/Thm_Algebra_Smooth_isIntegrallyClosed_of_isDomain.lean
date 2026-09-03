import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Smooth_isIntegrallyClosed_of_isDomain

universe u

theorem Algebra.Smooth.isIntegrallyClosed_of_isDomain (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Smooth R S] : IsIntegrallyClosed S := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Smooth_isIntegrallyClosed_of_isDomain.solution
