import Mathlib
import Theorems.Thm_ZMod_prime_dvd_eq_two_or_mod_four_eq_one_of_sq_add_one_eq_zero
import P2M.Util
namespace P2MW.S_ZMod_not_exists_sq_add_one_eq_zero_of_not_two_dvd_of_exists_prime_dvd_mod_four_ne_one

set_option autoImplicit false

theorem solution
    (M : ℕ) (hM : ¬ 2 ∣ M) (hℓ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 4 ≠ 1) :
    ¬ ∃ x : ZMod M, x ^ 2 + 1 = 0 := by
  rintro ⟨x, hx⟩
  obtain ⟨ℓ, hℓp, hℓM, hℓ4⟩ := hℓ
  rcases ZMod.prime_dvd_eq_two_or_mod_four_eq_one_of_sq_add_one_eq_zero x hx hℓp hℓM with h | h
  · subst h; exact hM hℓM
  · exact hℓ4 h
