import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_six_of_j_eq_zero

theorem WeierstrassCurve.natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_six_of_j_eq_zero
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj : E.j = 0) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) =
      Nat.card (rootsOfUnity 6 F) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_natCard_rootsOfUnity_six_of_j_eq_zero.solution
