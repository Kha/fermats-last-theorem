import Mathlib
import P2M.Util
import P2M.Sol.S_Padic_exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two

theorem Padic.exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b : ℚ_[p]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (∃ z x y : ℚ_[p], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (p * a) * x ^ 2 - b * y ^ 2 = 0) ↔ IsSquare b := by p2m_exact_reverting @_root_.P2MW.S_Padic_exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two.solution
