import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import P2M.Util
import P2M.Sol.S_Matrix_aeval_const_term_eq_zero_of_forall_pos

theorem
Matrix.aeval_const_term_eq_zero_of_forall_pos
    {R d : ℕ} (M : Fin (d + 1) → Matrix (Fin R) (Fin R) ℂ) (q : Polynomial ℂ)
    (h : ∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (d + 1), ((y : ℂ) ^ (a : ℕ)) • M a) q = 0) :
    Polynomial.aeval (M 0) q = 0 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_aeval_const_term_eq_zero_of_forall_pos.solution
