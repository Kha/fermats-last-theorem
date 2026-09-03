import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_separated_recurrence

set_option autoImplicit false

theorem Polynomial.exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_separated_recurrence
    (A : ℤ × ℤ → ℂ) (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ)
    (hD₁ : D₁.eval 0 ≠ 0) (hD₂ : D₂.eval 0 ≠ 0)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0)
    (hrec : ∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
      ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
        D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0) :
    ∃ P : MvPolynomial (Fin 4) ℂ, ∀ b₁ b₂ : ℂ, ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ =>
        ‖A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) *
          (∑ i ∈ Finset.range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ,
          A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) *
            (∑ i ∈ Finset.range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) * X ^ m.1 * Y ^ m.2) *
        (D₁.eval (b₁ * X) * D₁.eval (b₂ * X) * D₂.eval Y) =
        MvPolynomial.eval (![X, Y, b₁, b₂] : Fin 4 → ℂ) P := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_separated_recurrence.solution
