import Mathlib
import P2M.Util
import P2M.Sol.S_PadicInt_dvd_of_one_add_prime_pow_eq_pow

theorem PadicInt.dvd_of_one_add_prime_pow_eq_pow {p : ℕ} [hp : Fact p.Prime]
    {j : ℕ} {z : ℤ_[p]} (h : (1 + p : ℤ_[p]) ^ j = z ^ p) : p ∣ j := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_dvd_of_one_add_prime_pow_eq_pow.solution
