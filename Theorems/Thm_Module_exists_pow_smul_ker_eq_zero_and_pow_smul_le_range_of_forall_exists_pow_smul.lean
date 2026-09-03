import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul

set_option autoImplicit false

universe u v w

theorem Module.exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul
    {R : Type u} [CommRing R] (S : Finset R) (J : Ideal R) (hJ : Ideal.span (S : Set R) = J)
    {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N]
    (u : M →ₗ[R] N)
    (hker : (LinearMap.ker u).FG) (hcoker : Module.Finite R (N ⧸ LinearMap.range u))
    (hk : ∀ a ∈ S, ∀ x : M, u x = 0 → ∃ k : ℕ, a ^ k • x = 0)
    (hc : ∀ a ∈ S, ∀ y : N, ∃ (k : ℕ) (x : M), u x = a ^ k • y) :
    ∃ N₀ : ℕ,
      (∀ x : M, u x = 0 → ∀ a ∈ J ^ N₀, a • x = 0) ∧
      (∀ (y : N), ∀ a ∈ J ^ N₀, ∃ x : M, u x = a • y) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_pow_smul_ker_eq_zero_and_pow_smul_le_range_of_forall_exists_pow_smul.solution
