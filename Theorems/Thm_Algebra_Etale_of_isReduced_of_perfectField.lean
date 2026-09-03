import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_of_isReduced_of_perfectField

set_option autoImplicit false

theorem Algebra.Etale.of_isReduced_of_perfectField
    (K B : Type*) [Field K] [PerfectField K] [CommRing B] [Algebra K B]
    [Module.Finite K B] [IsReduced B] : Algebra.Etale K B := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_of_isReduced_of_perfectField.solution
