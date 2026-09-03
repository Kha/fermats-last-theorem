import Definitions.Def_ModularCurve_MultCoveringFamily
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_goodFamily_zero_eq_one

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.goodFamily_zero_eq_one (p : ℕ) [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r) :
    ∀ l : Fin r, (l : ℕ) = 0 → goodFamily Φ l = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_goodFamily_zero_eq_one.solution
