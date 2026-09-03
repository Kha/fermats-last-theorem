import Mathlib
import P2M.Util
import P2M.Sol.S_TrivSqZeroExt_isLocalRing

set_option autoImplicit false

theorem TrivSqZeroExt.isLocalRing {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [IsLocalRing R] : IsLocalRing (TrivSqZeroExt R M) := by p2m_exact_reverting @_root_.P2MW.S_TrivSqZeroExt_isLocalRing.solution
