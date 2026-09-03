import Mathlib
import P2M.Util
import P2M.Sol.S_Module_End_eq_one_of_pow_eq_one_of_forall_exists_sub_eq_prime_pow_smul

set_option autoImplicit false

theorem Module.End.eq_one_of_pow_eq_one_of_forall_exists_sub_eq_prime_pow_smul
    {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {p : ℕ} (hp : p.Prime) (a : ℕ) (ha : 1 ≤ a) (ha2 : p = 2 → 2 ≤ a)
    (htf : ∀ x : M, p • x = 0 → x = 0)
    (hsep : ∀ x : M, (∀ n : ℕ, ∃ y : M, x = p ^ n • y) → x = 0)
    (u : M →ₗ[R] M) (m : ℕ) (hm : m ≠ 0) (hu : u ^ m = 1)
    (hcong : ∀ x : M, ∃ y : M, u x - x = p ^ a • y) :
    u = 1 := by p2m_exact_reverting @_root_.P2MW.S_Module_End_eq_one_of_pow_eq_one_of_forall_exists_sub_eq_prime_pow_smul.solution
