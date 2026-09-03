import Mathlib
import Definitions.Def_ModularCurve_MultCoveringLink
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_linkBudget_spec
set_option autoImplicit false

open AlgebraicCurve open ModularCurve.MultCovering hiding exists_linkBudget

theorem ModularCurve.MultCovering.linkBudget_spec {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∀ i j, (p : AlgebraicClosure ℚ) ^ linkBudget Φ s hs * linkMatrix Φ s hs i j ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ linkBudget Φ s hs * linkMatrixInv Φ s hs i j ∈ A := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_linkBudget_spec.solution
