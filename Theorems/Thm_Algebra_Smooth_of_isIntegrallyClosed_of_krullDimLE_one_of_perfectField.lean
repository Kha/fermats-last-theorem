import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Smooth_of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField

set_option autoImplicit false

universe u v

theorem Algebra.Smooth.of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField
    (k : Type u) [Field k] [PerfectField k] (B : Type v) [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsIntegrallyClosed B] [Ring.KrullDimLE 1 B] :
    Algebra.Smooth k B := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Smooth_of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField.solution
