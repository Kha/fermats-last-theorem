import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Data.Int.ModEq
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_eq_shortModel

theorem WeierstrassCurve.exists_variableChange_eq_shortModel {K : Type*} [Field K] [CharZero K] (W : WeierstrassCurve K) : ∃ C : WeierstrassCurve.VariableChange K, C • W = ⟨0, 0, 0, -27 * W.c₄, -54 * W.c₆⟩ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_eq_shortModel.solution
