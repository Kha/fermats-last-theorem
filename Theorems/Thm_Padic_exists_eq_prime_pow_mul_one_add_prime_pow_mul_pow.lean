import Mathlib
import P2M.Util
import P2M.Sol.S_Padic_exists_eq_prime_pow_mul_one_add_prime_pow_mul_pow

theorem Padic.exists_eq_prime_pow_mul_one_add_prime_pow_mul_pow {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃ i < p, ∃ j < p, ∃ y : ℚ_[p], y ≠ 0 ∧
      x = (p : ℚ_[p]) ^ i * (1 + p : ℚ_[p]) ^ j * y ^ p := by p2m_exact_reverting @_root_.P2MW.S_Padic_exists_eq_prime_pow_mul_one_add_prime_pow_mul_pow.solution
