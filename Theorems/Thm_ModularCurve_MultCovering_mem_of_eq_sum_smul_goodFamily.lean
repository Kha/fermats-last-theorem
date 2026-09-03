import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringFamily
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_mem_of_eq_sum_smul_goodFamily

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.mem_of_eq_sum_smul_goodFamily (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Ψ : FamCtx p r) (c : Fin r → AlgebraicClosure ℚ) (x : ↥(modularFunctionFieldBar (1 * p)))
    (hx : x ∈ (infChart Γ).integers) (heq : x = ∑ j, c j • Ψ.t j) :
    ∀ j, c j ∈ A := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_mem_of_eq_sum_smul_goodFamily.solution
