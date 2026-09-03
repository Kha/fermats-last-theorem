import Mathlib
import P2M.Util
import P2M.Sol.S_Int_exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero

theorem Int.exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero (t q : ℤ) (hD : t ^ 2 - 4 * q ≠ 0) (p : ℕ) [Fact p.Prime] (h : ∃ a₀ : ℤ, ¬ (p : ℤ) ∣ a₀ ^ 2 + t * a₀ + q) : ∃ a : ℤ, ¬ (p : ℤ) ∣ a ^ 2 + t * a + q ∧ 2 ≤ a ^ 2 + t * a + q ∧ ¬ IsSquare (a ^ 2 + t * a + q) ∧ ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ 2 * a + t → ¬ (ℓ : ℤ) ^ 2 ∣ a ^ 2 + t * a + q := by p2m_exact_reverting @_root_.P2MW.S_Int_exists_not_dvd_and_le_and_not_isSquare_and_forall_prime_of_sq_sub_four_mul_ne_zero.solution
