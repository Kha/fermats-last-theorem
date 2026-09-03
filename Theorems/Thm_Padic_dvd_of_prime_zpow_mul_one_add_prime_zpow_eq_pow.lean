import Mathlib
import P2M.Util
import P2M.Sol.S_Padic_dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow

theorem Padic.dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow {p : ℕ} [hp : Fact p.Prime]
    {i j : ℤ} {y : ℚ_[p]}
    (h : (p : ℚ_[p]) ^ i * (1 + p : ℚ_[p]) ^ j = y ^ p) :
    (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by p2m_exact_reverting @_root_.P2MW.S_Padic_dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow.solution
