import Mathlib
import Theorems.Thm_ZMod_prime_dvd_eq_three_or_mod_three_eq_one_of_sq_add_self_add_one_eq_zero
import P2M.Util
namespace P2MW.S_ZMod_not_exists_sq_add_self_add_one_eq_zero_of_not_three_dvd_of_exists_prime_dvd_mod_three_ne_one

set_option autoImplicit false

theorem solution
    (M : ℕ) (hM : ¬ 3 ∣ M) (hℓ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 3 ≠ 1) :
    ¬ ∃ x : ZMod M, x ^ 2 + x + 1 = 0 := by
  rintro ⟨x, hx⟩
  obtain ⟨ℓ, hℓp, hℓM, hℓ3⟩ := hℓ
  rcases ZMod.prime_dvd_eq_three_or_mod_three_eq_one_of_sq_add_self_add_one_eq_zero x hx hℓp hℓM with h | h
  · subst h; exact hM hℓM
  · exact hℓ3 h
