import Mathlib
import P2M.Util
import P2M.Sol.S_PadicInt_exists_eq_one_add_prime_pow_mul_pow

theorem PadicInt.exists_eq_one_add_prime_pow_mul_pow {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {u : ℤ_[p]} (hu : ‖u‖ = 1) :
    ∃ j < p, ∃ z : ℤ_[p], u = (1 + p : ℤ_[p]) ^ j * z ^ p := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_exists_eq_one_add_prime_pow_mul_pow.solution
