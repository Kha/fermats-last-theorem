import Mathlib
import P2M.Util
import P2M.Sol.S_IsIntegrallyClosed_of_faithfullyFlat
set_option autoImplicit false

theorem IsIntegrallyClosed.of_faithfullyFlat (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.FaithfullyFlat A B] [IsIntegrallyClosed B] : IsIntegrallyClosed A := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_of_faithfullyFlat.solution
