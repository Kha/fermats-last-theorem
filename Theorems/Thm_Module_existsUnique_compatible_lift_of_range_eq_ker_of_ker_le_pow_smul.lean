import Mathlib
import P2M.Util
import P2M.Sol.S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul

set_option autoImplicit false

universe u

theorem Module.existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul
    {R : Type u} [CommRing R] (I : Ideal R)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1))))
    (P : ℕ → Type u) [∀ k, AddCommGroup (P k)] [∀ k, Module R (P k)] (π : ∀ k, P (k + 1) →ₗ[R] P k)
    (C : ℕ → Type u) [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)] (θ : ∀ k, P k →ₗ[R] C k)
    (u : ∀ k, E k →ₗ[R] P k) (huc : ∀ k, π k ∘ₗ u (k + 1) = u k ∘ₗ τ k)
    (hur : ∀ k, LinearMap.range (u k) = LinearMap.ker (θ k))
    (hui : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (u (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule R (E (k + c))))
    (p : ∀ k, P k) (hp : ∀ k, π k (p (k + 1)) = p k) (hpθ : ∀ k, θ k (p k) = 0) :
    ∃! e : ∀ k, E k, (∀ k, τ k (e (k + 1)) = e k) ∧ ∀ k, u k (e k) = p k := by p2m_exact_reverting @_root_.P2MW.S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul.solution
