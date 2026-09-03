import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_twentyFour_of_j_eq_zero_of_charP_two

set_option autoImplicit false

theorem WeierstrassCurve.natCard_stabilizer_variableChange_eq_twentyFour_of_j_eq_zero_of_charP_two
    {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
    (E : WeierstrassCurve F) [E.IsElliptic] (hj : E.j = 0) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) = 24 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_twentyFour_of_j_eq_zero_of_charP_two.solution
