import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_GeneralLinearGroup_exists_normal_relIndex_ne_zero_forall_isOfFinOrder_imp_eq_one_of_fg

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.GeneralLinearGroup.exists_normal_relIndex_ne_zero_forall_isOfFinOrder_imp_eq_one_of_fg
    (K : Type) [Field K] [CharZero K] (n : Type) [Fintype n] [DecidableEq n]
    (Γ : Subgroup (Matrix.GeneralLinearGroup n K)) (hΓ : Γ.FG) :
    ∃ N : Subgroup (Matrix.GeneralLinearGroup n K), N ≤ Γ ∧ (N.subgroupOf Γ).Normal ∧ N.relIndex Γ ≠ 0 ∧
      ∀ g ∈ N, IsOfFinOrder g → g = 1 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_GeneralLinearGroup_exists_normal_relIndex_ne_zero_forall_isOfFinOrder_imp_eq_one_of_fg.solution
