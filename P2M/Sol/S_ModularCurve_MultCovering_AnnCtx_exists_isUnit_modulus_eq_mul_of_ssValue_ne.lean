import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_JWidth
import P2M.Util
namespace P2MW.S_ModularCurve_MultCovering_AnnCtx_exists_isUnit_modulus_eq_mul_of_ssValue_ne
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (e : Fin (mAnnuli p))
    (he0 : ssValue Γ e ≠ 0) (he1728 : ssValue Γ e ≠ 1728) :
    ∃ u : ↥A, IsUnit u ∧ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * u := by
  refine ⟨1, isUnit_one, ?_⟩
  show ((Δ.An e).modulus : AlgebraicClosure ℚ) = _
  rw [Δ.modulus_eq e, jWidth_of_ne he0 he1728]; push_cast; ring
