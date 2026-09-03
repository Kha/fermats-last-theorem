import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_eq_C_mul_X_add_X_pow_of_totalDegree_le_of_forall_eval_eq_pow_mul_eval

set_option autoImplicit false

theorem MvPolynomial.exists_eq_C_mul_X_add_X_pow_of_totalDegree_le_of_forall_eval_eq_pow_mul_eval
    (g n : ℕ) (hn : 2 ≤ n) (α β : ℕ) (hαβ : α + β = n ^ 2) (hα : α = β + n)
    (P : MvPolynomial (Fin 2) ℚ) (hP : P.totalDegree ≤ g)
    (h : ∀ a b : ℕ,
      MvPolynomial.eval ![((α * a + β * b : ℕ) : ℚ), ((β * a + α * b : ℕ) : ℚ)] P =
        (n : ℚ) ^ (2 * g) * MvPolynomial.eval ![(a : ℚ), (b : ℚ)] P) :
    ∃ c : ℚ, P = MvPolynomial.C c * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ g := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_eq_C_mul_X_add_X_pow_of_totalDegree_le_of_forall_eval_eq_pow_mul_eval.solution
