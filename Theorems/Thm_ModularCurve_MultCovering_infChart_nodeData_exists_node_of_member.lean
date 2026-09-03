import Definitions.Def_ModularCurve_MultCoveringFamily
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_infChart_nodeData_exists_node_of_member
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.infChart_nodeData_exists_node_of_member (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r) :
    ∃ hint : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers,
      ∀ l : Fin r, 1 ≤ (l : ℕ) → ∃ e : Fin (mAnnuli p),
        (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint l⟩) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_infChart_nodeData_exists_node_of_member.solution
