import Mathlib
import P2M.Util
import P2M.Sol.S_IsGaloisGroup_isIntegrallyClosed_of_isIntegrallyClosed

set_option autoImplicit false

theorem IsGaloisGroup.isIntegrallyClosed_of_isIntegrallyClosed
    (G : Type*) [Group G] {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [MulSemiringAction G B] [IsGaloisGroup G A B]
    [IsIntegrallyClosed B] : IsIntegrallyClosed A := by p2m_exact_reverting @_root_.P2MW.S_IsGaloisGroup_isIntegrallyClosed_of_isIntegrallyClosed.solution
