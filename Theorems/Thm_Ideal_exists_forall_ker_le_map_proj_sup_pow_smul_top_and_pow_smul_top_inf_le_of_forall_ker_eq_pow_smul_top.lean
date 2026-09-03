import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top

set_option autoImplicit false

universe u v

theorem Ideal.exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    (F P : ℕ → Type v)
    [∀ n, AddCommGroup (F n)] [∀ n, Module B (F n)] [∀ n, Module.Finite B (F n)]
    [∀ n, AddCommGroup (P n)] [∀ n, Module B (P n)] [∀ n, Module.Finite B (P n)]
    (φ : ∀ n, F (n + 1) →ₗ[B] F n) (hφs : ∀ n, Function.Surjective (φ n))
    (hφk : ∀ n, LinearMap.ker (φ n) = J ^ (n + 1) • (⊤ : Submodule B (F (n + 1))))
    (π : ∀ n, P (n + 1) →ₗ[B] P n) (hπs : ∀ n, Function.Surjective (π n))
    (hπk : ∀ n, LinearMap.ker (π n) = J ^ (n + 1) • (⊤ : Submodule B (P (n + 1))))
    (u : ∀ n, F n →ₗ[B] P n) (hu : ∀ n, π n ∘ₗ u (n + 1) = u n ∘ₗ φ n)
    (K : Submodule B (∀ n, F n))
    (hK : ∀ x : ∀ n, F n, x ∈ K ↔ (∀ n, φ n (x (n + 1)) = x n) ∧ ∀ n, u n (x n) = 0) :
    ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
      LinearMap.ker (u n) ≤ K.map (LinearMap.proj n) ⊔ J ^ (k + 1) • (⊤ : Submodule B (F n)) ∧
      J ^ n • (⊤ : Submodule B (F n)) ⊓ K.map (LinearMap.proj n) ≤ J ^ k • K.map (LinearMap.proj n) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_forall_ker_le_map_proj_sup_pow_smul_top_and_pow_smul_top_inf_le_of_forall_ker_eq_pow_smul_top.solution
