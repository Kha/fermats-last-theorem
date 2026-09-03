import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_faithfulSMul

theorem IsIntegrallyClosed.of_isIntegrallyClosedIn_of_faithfulSMul
    (A F : Type*) [CommRing A] [IsDomain A] [Field F] [Algebra A F] [FaithfulSMul A F]
    [IsIntegrallyClosedIn A F] : IsIntegrallyClosed A := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_faithfulSMul.solution
