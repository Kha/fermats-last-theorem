import Definitions.Def_ModularCurve_MultCoveringFamily
import P2M.Util
namespace P2MW.S_ModularCurve_MultCovering_goodFamily_zero_eq_one

set_option autoImplicit false
set_option Elab.async false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (p : ℕ) [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r) :
    ∀ l : Fin r, (l : ℕ) = 0 → goodFamily Φ l = 1 :=
  Φ.t_zero
