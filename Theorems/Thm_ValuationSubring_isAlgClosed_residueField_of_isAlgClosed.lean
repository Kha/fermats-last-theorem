import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed

set_option autoImplicit false

theorem ValuationSubring.isAlgClosed_residueField_of_isAlgClosed
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) :
    IsAlgClosed (IsLocalRing.ResidueField ↥A) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed.solution
