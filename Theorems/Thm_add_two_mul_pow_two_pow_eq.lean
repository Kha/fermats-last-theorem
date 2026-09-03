import Mathlib
import P2M.Util
import P2M.Sol.S_add_two_mul_pow_two_pow_eq

universe u

theorem add_two_mul_pow_two_pow_eq
    {A : Type u} [CommRing A] (n : ℕ) (hn : 1 ≤ n) (u v : A) :
    ∃ w : A, (u + 2 * v) ^ (2 ^ n) =
      u ^ (2 ^ n) + 2 ^ (n + 1) * (u ^ (2 ^ n - 1) * v + u ^ (2 ^ n - 2) * v ^ 2) + 2 ^ (n + 2) * w := by p2m_exact_reverting @_root_.P2MW.S_add_two_mul_pow_two_pow_eq.solution
