import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_smul_eq_nodeNormalForm_of_not_isElliptic_of_c4_ne_zero

theorem WeierstrassCurve.exists_variableChange_smul_eq_nodeNormalForm_of_not_isElliptic_of_c4_ne_zero
    {K : Type*} [Field K] [CharZero K] (W : WeierstrassCurve K)
    (hW : ¬ W.IsElliptic) (hc4 : W.c₄ ≠ 0) :
    ∃ (c : K) (_ : c ≠ 0) (C : WeierstrassCurve.VariableChange K),
      C • W = (⟨0, c, 0, 0, 0⟩ : WeierstrassCurve K) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_nodeNormalForm_of_not_isElliptic_of_c4_ne_zero.solution
