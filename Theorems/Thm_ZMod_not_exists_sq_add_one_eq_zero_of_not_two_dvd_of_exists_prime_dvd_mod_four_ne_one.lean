import Mathlib
import P2M.Util
import P2M.Sol.S_ZMod_not_exists_sq_add_one_eq_zero_of_not_two_dvd_of_exists_prime_dvd_mod_four_ne_one

set_option autoImplicit false

theorem ZMod.not_exists_sq_add_one_eq_zero_of_not_two_dvd_of_exists_prime_dvd_mod_four_ne_one
    (M : ℕ) (hM : ¬ 2 ∣ M) (hℓ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 4 ≠ 1) :
    ¬ ∃ x : ZMod M, x ^ 2 + 1 = 0 := by p2m_exact_reverting @_root_.P2MW.S_ZMod_not_exists_sq_add_one_eq_zero_of_not_two_dvd_of_exists_prime_dvd_mod_four_ne_one.solution
