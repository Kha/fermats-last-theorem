import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_polynomial_forall_tsum_row_mul_eval_eq_and_tsum_mul_eval_eq_of_tsum_mul_eval_eq

set_option autoImplicit false

theorem MvPolynomial.exists_polynomial_forall_tsum_row_mul_eval_eq_and_tsum_mul_eval_eq_of_tsum_mul_eval_eq
    (A : ℕ × ℕ → ℂ) (D₁ D₂ : Polynomial ℂ) (P : MvPolynomial (Fin 2) ℂ) (r : ℝ)
    (hD₂ : D₂.eval 0 ≠ 0) (hr : 0 < r)
    (h : ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ => ‖A m * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ, A m * X ^ m.1 * Y ^ m.2) * (D₁.eval X * D₂.eval Y) = MvPolynomial.eval ![X, Y] P) :
    ∃ (q : ℕ → Polynomial ℂ) (r₂ : ℝ), 0 < r₂ ∧
      (∀ (j : ℕ) (X : ℂ), ‖X‖ < r →
        Summable (fun m₁ : ℕ => ‖A (m₁, j) * X ^ m₁‖) ∧
        (∑' m₁ : ℕ, A (m₁, j) * X ^ m₁) * D₁.eval X = (q j).eval X) ∧
      (∀ X Y : ℂ, ‖Y‖ < r₂ →
        Summable (fun j : ℕ => ‖(q j).eval X * Y ^ j‖) ∧
        (∑' j : ℕ, (q j).eval X * Y ^ j) * D₂.eval Y = MvPolynomial.eval ![X, Y] P) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_polynomial_forall_tsum_row_mul_eval_eq_and_tsum_mul_eval_eq_of_tsum_mul_eval_eq.solution
