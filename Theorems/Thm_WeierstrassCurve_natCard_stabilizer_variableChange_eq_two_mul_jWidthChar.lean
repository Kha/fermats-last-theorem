import Mathlib
import Definitions.Def_ModularCurve_PlaceWidthChar
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_mul_jWidthChar

set_option autoImplicit false

theorem WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_mul_jWidthChar
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (E : WeierstrassCurve K) [E.IsElliptic] :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange K) E) = 2 * ModularCurve.jWidthChar p E.j := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_mul_jWidthChar.solution
