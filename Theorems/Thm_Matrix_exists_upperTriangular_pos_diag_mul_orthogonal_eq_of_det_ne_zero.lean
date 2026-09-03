import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero

set_option autoImplicit false

theorem Matrix.exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) :
    ∃ b o : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j : Fin n, j < i → b i j = 0) ∧ (∀ i : Fin n, 0 < b i i) ∧
      (∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0) ∧ A = b * o := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_upperTriangular_pos_diag_mul_orthogonal_eq_of_det_ne_zero.solution
