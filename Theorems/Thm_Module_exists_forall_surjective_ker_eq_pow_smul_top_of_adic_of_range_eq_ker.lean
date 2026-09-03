import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker

set_option autoImplicit false

universe u

theorem Module.exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M N K : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [AddCommGroup K] [Module R K]
    (ρ : M →ₗ[R] N) (ι : K →ₗ[R] M) (hι : Function.Injective ι) (hιr : LinearMap.range ι = LinearMap.ker ρ)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1))))
    (P : ℕ → Type u) [∀ k, AddCommGroup (P k)] [∀ k, Module R (P k)] (π : ∀ k, P (k + 1) →ₗ[R] P k)
    (ψP : ∀ k, M →ₗ[R] P k) (hψPs : ∀ k, Function.Surjective (ψP k))
    (hψPk : ∀ k, LinearMap.ker (ψP k) = I ^ (k + 1) • (⊤ : Submodule R M))
    (hψPc : ∀ k, π k ∘ₗ ψP (k + 1) = ψP k)
    (C : ℕ → Type u) [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)] (γ : ∀ k, C (k + 1) →ₗ[R] C k)
    (ψC : ∀ k, N →ₗ[R] C k) (hψCs : ∀ k, Function.Surjective (ψC k))
    (hψCk : ∀ k, LinearMap.ker (ψC k) = I ^ (k + 1) • (⊤ : Submodule R N))
    (hψCc : ∀ k, γ k ∘ₗ ψC (k + 1) = ψC k)
    (θ : ∀ k, P k →ₗ[R] C k) (hθ : ∀ k, θ k ∘ₗ ψP k = ψC k ∘ₗ ρ)
    (u : ∀ k, E k →ₗ[R] P k) (huc : ∀ k, π k ∘ₗ u (k + 1) = u k ∘ₗ τ k)
    (hur : ∀ k, LinearMap.range (u k) = LinearMap.ker (θ k))
    (hui : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (u (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule R (E (k + c)))) :
    ∃ ψ : ∀ k, K →ₗ[R] E k,
      (∀ k, Function.Surjective (ψ k)) ∧
      (∀ k, LinearMap.ker (ψ k) = I ^ (k + 1) • (⊤ : Submodule R K)) ∧
      (∀ k, τ k ∘ₗ ψ (k + 1) = ψ k) ∧
      (∀ k, u k ∘ₗ ψ k = ψP k ∘ₗ ι) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_forall_surjective_ker_eq_pow_smul_top_of_adic_of_range_eq_ker.solution
