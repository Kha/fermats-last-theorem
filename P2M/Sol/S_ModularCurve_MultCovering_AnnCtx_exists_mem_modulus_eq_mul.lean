import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_JWidth
import P2M.Util
namespace P2MW.S_ModularCurve_MultCovering_AnnCtx_exists_mem_modulus_eq_mul
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) : ∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
    ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * a := by
  intro e
  have hmod : ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    show ((Δ.An e).modulus : AlgebraicClosure ℚ) = _
    rw [Δ.modulus_eq e]; push_cast; rfl
  have hpos : 1 ≤ jWidth (ssValue Γ e) := jWidth_pos (ssValue Γ e)
  refine ⟨(p : AlgebraicClosure ℚ) ^ (jWidth (ssValue Γ e) - 1), pow_mem (natCast_mem A p) _, ?_⟩
  rw [hmod, ← pow_succ', Nat.sub_add_cancel hpos]
