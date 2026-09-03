import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.AnnCtx.exists_mem_dom_abv_evalAt_param_ne
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    {Γ : ChartCtx p A} (Δ : AnnCtx Γ) (e : Fin (mAnnuli p))
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    ∃ Q₁ ∈ (Δ.annIn e).dom, ∃ Q₂ ∈ (Δ.annIn e).dom,
      μ (Q₁.evalAt (Δ.annIn e).param) ≠ μ (Q₂.evalAt (Δ.annIn e).param) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne.solution
