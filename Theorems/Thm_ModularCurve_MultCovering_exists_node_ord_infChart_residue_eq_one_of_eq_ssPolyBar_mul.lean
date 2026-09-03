import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import P2M.Util
import P2M.Sol.S_ModularCurve_MultCovering_exists_node_ord_infChart_residue_eq_one_of_eq_ssPolyBar_mul
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.exists_node_ord_infChart_residue_eq_one_of_eq_ssPolyBar_mul
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (f : ↥(modularFunctionFieldBar (1 * p))) (hf : f ∈ (infChart Γ).integers)
    (P : Polynomial (IsLocalRing.ResidueField ↥A)) (hP0 : P ≠ 0) (hdeg : P.natDegree + 1 ≤ mAnnuli p)
    (hres : (infChart Γ).residue ⟨f, hf⟩ = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) P) :
    ∃ e : Fin (mAnnuli p), (nodeTgt Γ e).ord ((infChart Γ).residue ⟨f, hf⟩) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_MultCovering_exists_node_ord_infChart_residue_eq_one_of_eq_ssPolyBar_mul.solution
