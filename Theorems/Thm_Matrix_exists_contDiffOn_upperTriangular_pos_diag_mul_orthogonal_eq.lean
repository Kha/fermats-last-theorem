import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq

set_option autoImplicit false

theorem Matrix.exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq
    (n : ℕ) :
    ∃ (b o : (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ)),
      ContDiffOn ℝ (⊤ : ℕ∞) b {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0} ∧
      ContDiffOn ℝ (⊤ : ℕ∞) o {A : Fin n → Fin n → ℝ | (Matrix.of A).det ≠ 0} ∧
      ∀ A : Fin n → Fin n → ℝ, (Matrix.of A).det ≠ 0 →
        (∀ i j : Fin n, j < i → b A i j = 0) ∧ (∀ i : Fin n, 0 < b A i i) ∧
        (∀ i j : Fin n, ∑ a : Fin n, o A a i * o A a j = if i = j then 1 else 0) ∧
        ∀ i j : Fin n, A i j = ∑ k : Fin n, b A i k * o A k j := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_contDiffOn_upperTriangular_pos_diag_mul_orthogonal_eq.solution
