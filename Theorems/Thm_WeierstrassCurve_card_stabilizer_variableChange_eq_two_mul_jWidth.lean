import Mathlib
import Definitions.Def_ModularCurve_JWidth
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_card_stabilizer_variableChange_eq_two_mul_jWidth

set_option autoImplicit false
theorem WeierstrassCurve.card_stabilizer_variableChange_eq_two_mul_jWidth
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (h2 : ringChar K ≠ 2) (h3 : ringChar K ≠ 3)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K) W) =
      2 * ModularCurve.jWidth W.j := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_card_stabilizer_variableChange_eq_two_mul_jWidth.solution
