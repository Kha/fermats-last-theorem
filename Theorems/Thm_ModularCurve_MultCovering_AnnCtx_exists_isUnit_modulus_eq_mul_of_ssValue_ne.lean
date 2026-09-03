import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_JWidth
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_AnnCtx_exists_isUnit_modulus_eq_mul_of_ssValue_ne
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.AnnCtx.exists_isUnit_modulus_eq_mul_of_ssValue_ne (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (e : Fin (mAnnuli p))
    (he0 : ssValue Γ e ≠ 0) (he1728 : ssValue Γ e ≠ 1728) :
    ∃ u : ↥A, IsUnit u ∧ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * u := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_AnnCtx_exists_isUnit_modulus_eq_mul_of_ssValue_ne.solution
