import Mathlib
import Definitions.Def_ModularCurve_MultCoveringLink
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_eq_sum_linkMatrix_smul_goodFamily
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.MultCovering.eq_sum_linkMatrix_smul_goodFamily {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    ∀ i, s i = ∑ j, linkMatrix Φ s hs i j • goodFamily Φ j := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_eq_sum_linkMatrix_smul_goodFamily.solution
