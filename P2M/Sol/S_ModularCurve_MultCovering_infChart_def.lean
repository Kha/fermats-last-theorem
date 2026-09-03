import Definitions.Def_ModularCurve_MultCoveringCharts
import P2M.Util
namespace P2MW.S_ModularCurve_MultCovering_infChart_def

set_option autoImplicit false

open AlgebraicCurve ModularCurve.MultCovering

set_option maxHeartbeats 3200000 in
theorem solution {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) :
    infChart Γ = ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply := rfl
