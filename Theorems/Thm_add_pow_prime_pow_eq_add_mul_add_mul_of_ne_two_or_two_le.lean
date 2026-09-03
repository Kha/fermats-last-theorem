import Mathlib
import P2M.Util
import P2M.Sol.S_add_pow_prime_pow_eq_add_mul_add_mul_of_ne_two_or_two_le

universe u

theorem add_pow_prime_pow_eq_add_mul_add_mul_of_ne_two_or_two_le
    {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime] (n r : ℕ) (hr : 1 ≤ r) (h2 : p ≠ 2 ∨ 2 ≤ r)
    (u v : A) :
    ∃ w : A, (u + (p : A) ^ r * v) ^ (p ^ n) =
      u ^ (p ^ n) + (p : A) ^ (n + r) * u ^ (p ^ n - 1) * v + (p : A) ^ (n + r + 1) * w := by p2m_exact_reverting @_root_.P2MW.S_add_pow_prime_pow_eq_add_mul_add_mul_of_ne_two_or_two_le.solution
