import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system

set_option autoImplicit false

universe u

theorem Module.exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1)))) :
    ∃ L : Submodule R (∀ k, E k),
      (∀ e : ∀ k, E k, e ∈ L ↔ ∀ k, τ k (e (k + 1)) = e k) ∧
      (∀ k, Function.Surjective ((LinearMap.proj k).comp L.subtype : L →ₗ[R] E k)) ∧
      (∀ k, LinearMap.ker ((LinearMap.proj k).comp L.subtype : L →ₗ[R] E k) =
        I ^ (k + 1) • (⊤ : Submodule R L)) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.solution
