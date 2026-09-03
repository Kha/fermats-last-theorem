import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_cuspInftyBar_mem_infChart_dom

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.MultCovering

theorem ModularCurve.MultCovering.cuspInftyBar_mem_infChart_dom
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) :
    cuspInftyBar (1 * p) ∈ (infChart Γ).dom := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_cuspInftyBar_mem_infChart_dom.solution
