import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_sub_one_pow_eq_zero_of_pow_sub_one_pow_eq_zero_of_eq_one_add_pow_smul

set_option autoImplicit false

theorem Module.End.sub_one_pow_eq_zero_of_pow_sub_one_pow_eq_zero_of_eq_one_add_pow_smul
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ℓ : ℕ} (hℓ : ℓ.Prime) {a : ℕ} (ha : 3 ≤ ℓ ^ a)
    (htf : ∀ x : M, (ℓ : R) • x = 0 → x = 0)
    (hsep : ∀ x : M, (∀ k : ℕ, ∃ z : M, (ℓ : R) ^ k • z = x) → x = 0)
    {m : ℕ} (hm : 0 < m) (hunit : ∀ r : ℕ, r.Prime → r ∣ m → r ≠ ℓ → IsUnit (r : R))
    (g y : Module.End R M) (hg : g = 1 + ((ℓ : R) ^ a) • y)
    {n : ℕ} (hn : (g ^ m - 1) ^ n = 0) : (g - 1) ^ n = 0 := by p2m_exact_reverting @_root_.P2MW.S_Module_End_sub_one_pow_eq_zero_of_pow_sub_one_pow_eq_zero_of_eq_one_add_pow_smul.solution
