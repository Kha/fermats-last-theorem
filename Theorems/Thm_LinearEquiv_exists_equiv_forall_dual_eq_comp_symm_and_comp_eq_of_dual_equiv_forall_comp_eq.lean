import Mathlib
import P2M.Util
import P2M.Sol.S_LinearEquiv_exists_equiv_forall_dual_eq_comp_symm_and_comp_eq_of_dual_equiv_forall_comp_eq

set_option autoImplicit false

open scoped TensorProduct

theorem LinearEquiv.exists_equiv_forall_dual_eq_comp_symm_and_comp_eq_of_dual_equiv_forall_comp_eq
    (R : Type*) [CommRing R] (k : Type*) [CommRing k] [Algebra R k]
    (Ω : Type*) [AddCommGroup Ω] [Module R Ω] [Module.Finite R Ω] [Module.Free R Ω]
    (S : Type*) [AddCommGroup S] [Module R S] [Module.Finite R S] [Module.Free R S]
    {ι : Type*} (a : ι → (Ω →ₗ[R] Ω)) (s : ι → (S →ₗ[R] S))
    (τ : Module.Dual R Ω ≃ₗ[R] Module.Dual R S)
    (hτ : ∀ (t : ι) (D : Module.Dual R Ω), τ (D ∘ₗ a t) = (τ D) ∘ₗ s t) :
    ∃ θ : Ω ≃ₗ[R] S,
      (∀ D : Module.Dual R Ω, τ D = D ∘ₗ (θ.symm : S →ₗ[R] Ω)) ∧
      (∀ t : ι, (θ : Ω →ₗ[R] S) ∘ₗ a t = s t ∘ₗ (θ : Ω →ₗ[R] S)) ∧
      ∃ Ξ : k ⊗[R] Ω ≃ₗ[k] k ⊗[R] S,
        (∀ (c : k) (x : Ω), Ξ (c ⊗ₜ x) = c ⊗ₜ θ x) ∧
        ∀ t : ι, (Ξ : k ⊗[R] Ω →ₗ[k] k ⊗[R] S) ∘ₗ (a t).baseChange k =
          (s t).baseChange k ∘ₗ (Ξ : k ⊗[R] Ω →ₗ[k] k ⊗[R] S) := by p2m_exact_reverting @_root_.P2MW.S_LinearEquiv_exists_equiv_forall_dual_eq_comp_symm_and_comp_eq_of_dual_equiv_forall_comp_eq.solution
