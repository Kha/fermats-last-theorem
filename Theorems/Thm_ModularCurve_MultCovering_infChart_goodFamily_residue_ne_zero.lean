import Definitions.Def_ModularCurve_MultCoveringFamily
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_infChart_goodFamily_residue_ne_zero
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve open ModularCurve.MultCovering hiding infChart_residue_goodFamily

theorem ModularCurve.MultCovering.infChart_goodFamily_residue_ne_zero (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r) :
    ∃ hint : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers,
      ∀ l, (infChart Γ).residue ⟨goodFamily Φ l, hint l⟩ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_infChart_goodFamily_residue_ne_zero.solution
