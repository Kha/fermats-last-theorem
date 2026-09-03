import Mathlib
import Definitions.Def_ModularCurve_MultCoveringLink
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_linkMatrixInv_mul
set_option autoImplicit false

open AlgebraicCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.linkMatrixInv_mul {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    linkMatrixInv Φ s hs * linkMatrix Φ s hs = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_linkMatrixInv_mul.solution
