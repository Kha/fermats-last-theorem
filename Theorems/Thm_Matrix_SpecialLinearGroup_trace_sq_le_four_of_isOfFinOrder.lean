import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_trace_sq_le_four_of_isOfFinOrder

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.SpecialLinearGroup.trace_sq_le_four_of_isOfFinOrder (γ : SL(2, ℤ)) (h : IsOfFinOrder γ) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_trace_sq_le_four_of_isOfFinOrder.solution
