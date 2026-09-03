import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top

set_option autoImplicit false

universe u v w

theorem Ideal.exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    (G : ℕ → Type v) (F : ℕ → Type w)
    [∀ k, AddCommGroup (G k)] [∀ k, Module B (G k)] [Module.Finite B (G 0)]
    [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)]
    (γ : ∀ k, G (k + 1) →ₗ[B] G k) (hγs : ∀ k, Function.Surjective (γ k))
    (hγk : ∀ k, LinearMap.ker (γ k) = J ^ (k + 1) • (⊤ : Submodule B (G (k + 1))))
    (φ : ∀ k, F (k + 1) →ₗ[B] F k)
    (hφk : ∀ k, LinearMap.ker (φ k) ≤ J ^ (k + 1) • (⊤ : Submodule B (F (k + 1))))
    (θ : ∀ k, G k →ₗ[B] F k) (hθs : ∀ k, Function.Surjective (θ k))
    (hθc : ∀ k, φ k ∘ₗ θ (k + 1) = θ k ∘ₗ γ k) :
    ∃ c : ℕ, ∀ k n : ℕ, k + c ≤ n →
      (J ^ n • (⊤ : Submodule B (G n))) ⊓ LinearMap.ker (θ n) ≤ J ^ k • LinearMap.ker (θ n) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_forall_pow_smul_top_inf_ker_le_pow_smul_ker_of_forall_ker_eq_pow_smul_top.solution
