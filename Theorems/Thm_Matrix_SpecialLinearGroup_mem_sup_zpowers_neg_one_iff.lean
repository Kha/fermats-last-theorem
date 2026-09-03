import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.SpecialLinearGroup.mem_sup_zpowers_neg_one_iff
    (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    g ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ↔ g ∈ Γ ∨ -g ∈ Γ := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_mem_sup_zpowers_neg_one_iff.solution
