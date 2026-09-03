import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import P2M.Util
namespace P2MW.S_ModularCurve_MultCovering_cuspInftyBar_mem_infChart_dom

set_option autoImplicit false
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.MultCovering

theorem solution
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) :
    cuspInftyBar (1 * p) ∈ (infChart Γ).dom :=
  ModularCurve.PlaceSpecialization.LevelOneProlongationPair.cuspInftyBar_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply
