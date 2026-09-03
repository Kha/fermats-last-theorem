import Mathlib
import P2M.Util
import P2M.Sol.S_ZMod_prime_dvd_eq_three_or_mod_three_eq_one_of_sq_add_self_add_one_eq_zero

set_option autoImplicit false

theorem ZMod.prime_dvd_eq_three_or_mod_three_eq_one_of_sq_add_self_add_one_eq_zero
    {M : ℕ} (x : ZMod M) (hx : x ^ 2 + x + 1 = 0)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) :
    ℓ = 3 ∨ ℓ % 3 = 1 := by p2m_exact_reverting @_root_.P2MW.S_ZMod_prime_dvd_eq_three_or_mod_three_eq_one_of_sq_add_self_add_one_eq_zero.solution
