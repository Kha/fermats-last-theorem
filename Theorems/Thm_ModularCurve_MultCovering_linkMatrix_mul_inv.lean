import Mathlib
import Definitions.Def_ModularCurve_MultCoveringLink
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_linkMatrix_mul_inv
set_option autoImplicit false

open AlgebraicCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.linkMatrix_mul_inv {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    linkMatrix Φ s hs * linkMatrixInv Φ s hs = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_linkMatrix_mul_inv.solution
