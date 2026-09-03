import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range

set_option autoImplicit false

universe u

theorem LinearMap.exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range
    {B : Type u} [CommRing B] [IsNoetherianRing B] (J : Ideal B)
    {GE GK : Type u} [AddCommGroup GE] [Module B GE] [AddCommGroup GK] [Module B GK] [Module.Finite B GK]
    {r : ℕ} (p : (Fin r → B) →ₗ[B] GE) (hp : Function.Surjective p)
    (F E : ℕ → Type u) [∀ k, AddCommGroup (F k)] [∀ k, Module B (F k)] [∀ k, AddCommGroup (E k)] [∀ k, Module B (E k)]
    (φ : ∀ k, F (k + 1) →ₗ[B] F k) (hφs : ∀ k, Function.Surjective (φ k))
    (hφk : ∀ k, LinearMap.ker (φ k) = J ^ (k + 1) • (⊤ : Submodule B (F (k + 1))))
    (ε : ∀ k, F k →ₗ[B] E k) (ψE : ∀ k, GE →ₗ[B] E k) (lam : ∀ k, GK →ₗ[B] F k)
    (hlamc : ∀ k, φ k ∘ₗ lam (k + 1) = lam k) (hlamr : ∀ k, LinearMap.range (lam k) = LinearMap.ker (ε k))

    (ℓ : ∀ n, (Fin r → B) →ₗ[B] F n) (hℓε : ∀ n, ε n ∘ₗ ℓ n = ψE n ∘ₗ p) (hℓφ : ∀ n, φ n ∘ₗ ℓ (n + 1) = ℓ n)
    (δs : ∀ n, ↥(LinearMap.ker p) →ₗ[B] GK) (hδs : ∀ n, lam n ∘ₗ δs n = ℓ n ∘ₗ (LinearMap.ker p).subtype)
    (hδsc : ∀ n, δs (n + 1) - δs n ∈ J ^ (n + 1) • (⊤ : Submodule B (↥(LinearMap.ker p) →ₗ[B] GK)))

    (δ : ↥(LinearMap.ker p) →ₗ[B] GK)
    (hδ : ∀ n, δ - δs n ∈ J ^ (n + 1) • (⊤ : Submodule B (↥(LinearMap.ker p) →ₗ[B] GK)) ⊔
      LinearMap.range (LinearMap.lcomp B GK (LinearMap.ker p).subtype)) :
    ∃ ℓ' : ∀ k, (Fin r → B) →ₗ[B] F k,
      (∀ k, φ k ∘ₗ ℓ' (k + 1) = ℓ' k) ∧
      (∀ k, ε k ∘ₗ ℓ' k = ψE k ∘ₗ p) ∧
      (∀ k, ℓ' k ∘ₗ (LinearMap.ker p).subtype = lam k ∘ₗ δ) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_forall_comp_eq_comp_subtype_eq_of_forall_sub_mem_pow_smul_sup_range.solution
