import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal

set_option autoImplicit false

theorem LinearMap.exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal
    {R : Type*} [CommRing R] [IsDomain R]
    {Γ : Type*} [Group Γ] {T : Type*} [AddCommGroup T] [Module R T]
    (ρ : Γ →* Module.End R T) (I : Subgroup Γ) (hI : I.Normal)
    (f : T →ₗ[R] R) (hf : ∀ τ ∈ I, f ∘ₗ ρ τ = f) :
    ∃ M : Submodule R T,
      (∀ x : T, x ∈ M ↔ ∀ γ : Γ, f (ρ γ x) = 0) ∧
      (∀ (γ : Γ) (x : T), x ∈ M → ρ γ x ∈ M) ∧
      (∀ τ ∈ I, ∀ x : T, ρ τ x - x ∈ M) ∧
      (∀ (r : R) (x : T), r ≠ 0 → r • x ∈ M → x ∈ M) ∧
      (∀ x ∈ M, f x = 0) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_submodule_mem_iff_forall_apply_eq_zero_of_forall_comp_eq_of_normal.solution
