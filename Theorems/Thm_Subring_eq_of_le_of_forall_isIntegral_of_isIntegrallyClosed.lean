import Mathlib
import P2M.Util
import P2M.Sol.S_Subring_eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed

set_option autoImplicit false

theorem Subring.eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed
    {F : Type*} [Field F] (Bflat B : Subring F) (hle : Bflat ≤ B)
    [IsFractionRing ↥Bflat F] [IsIntegrallyClosed ↥Bflat]
    (hint : ∀ b ∈ B, IsIntegral ↥Bflat b) :
    B = Bflat := by p2m_exact_reverting @_root_.P2MW.S_Subring_eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed.solution
