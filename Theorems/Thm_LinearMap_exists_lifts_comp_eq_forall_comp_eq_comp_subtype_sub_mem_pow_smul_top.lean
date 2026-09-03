import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {GE GK : Type v} [AddCommGroup GE] [Module B GE] [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    {r : ℕ} (p : (Fin r → B) →ₗ[B] GE)
    (F E : ℕ → Type w) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)] [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (φ : ∀ k, F (k + 1) →ₗ[B] F k) (hφs : ∀ k, Function.Surjective (φ k))
    (hφk : ∀ k, LinearMap.ker (φ k) = J ^ (k + 1) • (⊤ : Submodule B (F (k + 1))))
    (τ : ∀ k, E (k + 1) →ₗ[B] E k)
    (hτk : ∀ k, LinearMap.ker (τ k) = J ^ (k + 1) • (⊤ : Submodule B (E (k + 1))))
    (ε : ∀ k, F k →ₗ[B] E k) (hεs : ∀ k, Function.Surjective (ε k))
    (hεc : ∀ k, τ k ∘ₗ ε (k + 1) = ε k ∘ₗ φ k)
    (ψE : ∀ k, GE →ₗ[B] E k) (hψEc : ∀ k, τ k ∘ₗ ψE (k + 1) = ψE k)
    (lam : ∀ k, GK →ₗ[B] F k) (hlamc : ∀ k, φ k ∘ₗ lam (k + 1) = lam k)
    (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))
    (hlami : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (lam (k + c)) ≤ J ^ (k + 1) • (⊤ : Submodule B GK)) :
    ∃ (ℓ : ∀ n : ℕ, (Fin r → B) →ₗ[B] F n) (δs : ∀ n : ℕ, ↥(LinearMap.ker p) →ₗ[B] GK),
      (∀ n, ε n ∘ₗ ℓ n = ψE n ∘ₗ p) ∧
      (∀ n, φ n ∘ₗ ℓ (n + 1) = ℓ n) ∧
      (∀ n, lam n ∘ₗ δs n = ℓ n ∘ₗ (LinearMap.ker p).subtype) ∧
      (∀ n, δs (n + 1) - δs n ∈ J ^ (n + 1) • (⊤ : Submodule B (↥(LinearMap.ker p) →ₗ[B] GK))) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_lifts_comp_eq_forall_comp_eq_comp_subtype_sub_mem_pow_smul_top.solution
