import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_eq_top_of_normal_of_exists_ne_one_ne_neg_one

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.SpecialLinearGroup.eq_top_of_normal_of_exists_ne_one_ne_neg_one
    {K : Type*} [Field K] (hK : 4 ≤ Cardinal.mk K)
    (N : Subgroup SL(2, K)) [N.Normal]
    (hN : ∃ g ∈ N, g ≠ 1 ∧ g ≠ -1) :
    N = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_eq_top_of_normal_of_exists_ne_one_ne_neg_one.solution
