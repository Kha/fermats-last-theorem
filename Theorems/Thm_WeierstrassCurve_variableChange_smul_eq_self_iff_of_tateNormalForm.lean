import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_variableChange_smul_eq_self_iff_of_tateNormalForm

open WeierstrassCurve in
theorem WeierstrassCurve.variableChange_smul_eq_self_iff_of_tateNormalForm
    {K : Type*} [Field K] (E : WeierstrassCurve K)
    (ha₁ : E.a₁ = 1) (ha₂ : E.a₂ = 0) (ha₃ : E.a₃ = 0)
    (hc₄ : E.c₄ ≠ 0) (hc₆ : E.c₆ ≠ 0)
    (C : VariableChange K) :
    C • E = E ↔ C = 1 ∨ C = (⟨-1, 0, -1, 0⟩ : VariableChange K) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_variableChange_smul_eq_self_iff_of_tateNormalForm.solution
