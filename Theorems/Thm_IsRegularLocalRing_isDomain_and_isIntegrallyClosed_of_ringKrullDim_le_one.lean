import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one

set_option autoImplicit false

theorem IsRegularLocalRing.isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one
    (A : Type*) [CommRing A] [IsRegularLocalRing A] (h : ringKrullDim A ≤ 1) :
    IsDomain A ∧ IsIntegrallyClosed A := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one.solution
