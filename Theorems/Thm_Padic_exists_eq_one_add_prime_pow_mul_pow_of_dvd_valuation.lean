import Mathlib
import P2M.Util
import P2M.Sol.S_Padic_exists_eq_one_add_prime_pow_mul_pow_of_dvd_valuation

set_option autoImplicit false
theorem Padic.exists_eq_one_add_prime_pow_mul_pow_of_dvd_valuation (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (a : ℚ_[p]) (ha : a ≠ 0) (hv : (p : ℤ) ∣ Padic.valuation a) :
    ∃ (r : ℕ) (w : ℚ_[p]), a = (1 + (p : ℚ_[p])) ^ r * w ^ p := by p2m_exact_reverting @_root_.P2MW.S_Padic_exists_eq_one_add_prime_pow_mul_pow_of_dvd_valuation.solution
