import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isField_of_isIntegrallyClosedIn_of_isArtinianRing_of_isReduced

set_option autoImplicit false

theorem IsLocalRing.isField_of_isIntegrallyClosedIn_of_isArtinianRing_of_isReduced
    {B F : Type*} [CommRing B] [IsLocalRing B] [CommRing F] [Nontrivial F] [Algebra B F]
    [IsArtinianRing F] [IsReduced F] (h : IsIntegrallyClosedIn B F) :
    IsField F := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isField_of_isIntegrallyClosedIn_of_isArtinianRing_of_isReduced.solution
