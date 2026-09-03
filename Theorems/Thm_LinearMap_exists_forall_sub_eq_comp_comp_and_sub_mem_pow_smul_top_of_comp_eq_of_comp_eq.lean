import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {GK : Type v} [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    {GE : Type v} [AddCommGroup GE] [Module B GE] [Module.Finite B GE]
    {M : Type v} [AddCommGroup M] [Module B M]
    (ϑ : GK →ₗ[B] M) (θE : M →ₗ[B] GE) (hex : LinearMap.range ϑ = LinearMap.ker θE) (hθE : Function.Surjective θE)
    (F : ℕ → Type w) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)]
    (φ : ∀ k, F (k + 1) →ₗ[B] F k) (hF : ∀ k, I ^ (k + 1) • (⊤ : Submodule B (F k)) = ⊥)
    (lam : ∀ k, GK →ₗ[B] F k) (hlamc : ∀ k, φ k ∘ₗ lam (k + 1) = lam k)
    (c : ℕ) (hlami : ∀ k, LinearMap.ker (lam (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule B GK))
    (E : ℕ → Type w) [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (ε : ∀ k, F k →ₗ[B] E k) (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))
    (θ θ' : ∀ k, M →ₗ[B] F k)
    (hθc : ∀ k, φ k ∘ₗ θ (k + 1) = θ k) (hθ'c : ∀ k, φ k ∘ₗ θ' (k + 1) = θ' k)
    (hθϑ : ∀ k, θ k ∘ₗ ϑ = lam k) (hθ'ϑ : ∀ k, θ' k ∘ₗ ϑ = lam k)
    (hθε : ∀ k, ε k ∘ₗ θ k = ε k ∘ₗ θ' k) :
    ∃ g : ℕ → (GE →ₗ[B] GK),
      (∀ k, g (k + 1) - g k ∈ I ^ (k + 1) • (⊤ : Submodule B (GE →ₗ[B] GK))) ∧
      (∀ k, θ' k - θ k = lam k ∘ₗ g k ∘ₗ θE) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_forall_sub_eq_comp_comp_and_sub_mem_pow_smul_top_of_comp_eq_of_comp_eq.solution
