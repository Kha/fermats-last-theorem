import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_specialLinearGroup_mul_upperTriangular

theorem Matrix.exists_specialLinearGroup_mul_upperTriangular (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) : ∃ (B : Matrix.SpecialLinearGroup (Fin 2) ℤ) (a b d : ℤ), 0 < a ∧ 0 ≤ b ∧ b < |d| ∧ a * d = M.det ∧ M = (B : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b; 0, d] := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_specialLinearGroup_mul_upperTriangular.solution
