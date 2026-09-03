import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_smul_eq_zero_of_c4_eq_zero_of_c6_eq_zero

theorem WeierstrassCurve.exists_variableChange_smul_eq_zero_of_c4_eq_zero_of_c6_eq_zero
    {L : Type*} [Field L] [CharZero L] (W : WeierstrassCurve L)
    (hc4 : W.c₄ = 0) (hc6 : W.c₆ = 0) :
    ∃ C : WeierstrassCurve.VariableChange L,
      C • W = (⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve L) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_zero_of_c4_eq_zero_of_c6_eq_zero.solution
