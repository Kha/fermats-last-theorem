import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_compConst_eq_compConst

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.compConst_eq_compConst (p : ℕ) [Fact p.Prime] {r : ℕ} (Φ Φ'' : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (hΓ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p →
      ∀ [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p], Nonempty (ChartCtx p A)) :
    compConst Φ s hs = compConst Φ'' s hs := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_compConst_eq_compConst.solution
