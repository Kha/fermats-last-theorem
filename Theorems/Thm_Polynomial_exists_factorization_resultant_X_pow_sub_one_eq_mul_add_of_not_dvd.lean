import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd

set_option autoImplicit false

theorem Polynomial.exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd
    (P : Polynomial ℤ) (hP : P.Monic) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ¬ ((ℓ : ℤ) ∣ P.coeff 0))
    (hres : ∀ n : ℕ, 0 < n → (Polynomial.X ^ n - 1 : Polynomial ℤ).resultant P ≠ 0) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∃ c : ℕ, ∀ j : ℕ, 0 < j → ¬ ℓ ∣ j → ∀ k : ℕ,
        ((Polynomial.X ^ (m₀ * j * ℓ ^ k) - 1 : Polynomial ℤ).resultant P).natAbs.factorization ℓ =
          P.natDegree * k + c := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd.solution
