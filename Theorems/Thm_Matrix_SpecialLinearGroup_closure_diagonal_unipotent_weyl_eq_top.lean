import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Algebra.Group.Subgroup.Lattice
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_closure_diagonal_unipotent_weyl_eq_top

open scoped MatrixGroups
theorem Matrix.SpecialLinearGroup.closure_diagonal_unipotent_weyl_eq_top
    {K : Type*} [Field K] :
    Subgroup.closure
      ({g : SL(2, K) | ∃ a : K, (g : Matrix (Fin 2) (Fin 2) K) = !![a, 0; 0, a⁻¹]} ∪
        {g : SL(2, K) | ∃ z : K, (g : Matrix (Fin 2) (Fin 2) K) = !![1, z; 0, 1]} ∪
        {g : SL(2, K) | (g : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0]}) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_closure_diagonal_unipotent_weyl_eq_top.solution
