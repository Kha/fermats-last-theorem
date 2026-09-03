import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_twelve_of_j_eq_zero_of_charP_three

set_option autoImplicit false

theorem WeierstrassCurve.natCard_stabilizer_variableChange_eq_twelve_of_j_eq_zero_of_charP_three
    {F : Type*} [Field F] [IsAlgClosed F] [CharP F 3]
    (E : WeierstrassCurve F) [E.IsElliptic] (hj : E.j = 0) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) = 12 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_twelve_of_j_eq_zero_of_charP_three.solution
