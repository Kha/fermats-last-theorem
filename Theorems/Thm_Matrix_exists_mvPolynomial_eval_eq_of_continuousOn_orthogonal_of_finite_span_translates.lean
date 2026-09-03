import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates

set_option autoImplicit false

theorem Matrix.exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates
    (n : ℕ) (f : (Fin n → Fin n → ℝ) → ℂ)
    (hf : ContinuousOn f {o : Fin n → Fin n → ℝ | ∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0})
    (hfin : ∃ (m : ℕ) (g : Fin m → (Fin n → Fin n → ℝ) → ℂ),
      ∀ r : Fin n → Fin n → ℝ, (∀ i j : Fin n, ∑ a : Fin n, r a i * r a j = if i = j then 1 else 0) →
        ∃ a : Fin m → ℂ, ∀ o : Fin n → Fin n → ℝ,
          (∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0) →
          f (fun i j => ∑ k : Fin n, o i k * r k j) = ∑ l, a l * g l o) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ o : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, ∑ a : Fin n, o a i * o a j = if i = j then 1 else 0) →
      f o = MvPolynomial.eval (fun ij : Fin n × Fin n => ((o ij.1 ij.2 : ℝ) : ℂ)) P := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_mvPolynomial_eval_eq_of_continuousOn_orthogonal_of_finite_span_translates.solution
