import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_place_toSubring_eq_of_isIntegrallyClosedIn_of_isNoetherianRing

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.exists_place_toSubring_eq_of_isIntegrallyClosedIn_of_isNoetherianRing
    {L F : Type*} [Field L] [IsAlgClosed L] [Field F] [Algebra L F] [IsCurveOver L F]
    (R : Subring F) [IsLocalRing ↥R] [IsNoetherianRing ↥R] [IsFractionRing ↥R F]
    (hn : IsIntegrallyClosedIn ↥R F)
    (hL : ∀ a : L, algebraMap L F a ∈ R) (hR : R ≠ ⊤) :
    ∃ P : Place L F, P.toValuationSubring.toSubring = R := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_place_toSubring_eq_of_isIntegrallyClosedIn_of_isNoetherianRing.solution
