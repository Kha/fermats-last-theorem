import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_ProjGenLinGroup_exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.ProjGenLinGroup.exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero
    (K : Type) [Field K] [CharZero K] (n : Type) [Fintype n] [DecidableEq n]
    (Γ : Subgroup (Matrix.ProjGenLinGroup n K)) (hΓ : Γ.FG) :
    ∃ N : Subgroup (Matrix.ProjGenLinGroup n K), N ≤ Γ ∧ (N.subgroupOf Γ).Normal ∧ N.relIndex Γ ≠ 0 ∧
      ∀ g ∈ N, IsOfFinOrder g → g = 1 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_ProjGenLinGroup_exists_torsionFree_normal_subgroup_finiteIndex_of_fg_charZero.solution
