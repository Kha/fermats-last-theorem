import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_mem_zeroChart_nodes_iff

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.mem_zeroChart_nodes_iff {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (x : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) :
    x ∈ (zeroChart Γ).nodes ↔
      ∃ a ∈ ssJSet p (IsLocalRing.ResidueField ↥A), charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p) = x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_mem_zeroChart_nodes_iff.solution
