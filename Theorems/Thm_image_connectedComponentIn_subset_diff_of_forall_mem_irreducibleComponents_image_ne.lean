import Mathlib
import P2M.Util
import P2M.Sol.S_image_connectedComponentIn_subset_diff_of_forall_mem_irreducibleComponents_image_ne

set_option autoImplicit false

universe u

theorem image_connectedComponentIn_subset_diff_of_forall_mem_irreducibleComponents_image_ne
    {X : Type u} [TopologicalSpace X] (Z₁ Z₂ : Set X)
    (hZ₁c : IsClosed Z₁) (hZ₂c : IsClosed Z₂) (hZ₁ : IsIrreducible Z₁) (hZ₂ : IsIrreducible Z₂)
    (hcov : Z₁ ∪ Z₂ = Set.univ) (h₁₂ : ¬ Z₁ ⊆ Z₂) (h₂₁ : ¬ Z₂ ⊆ Z₁)
    (τ : X ≃ₜ X) (hτ : ∀ Z ∈ irreducibleComponents X, τ '' Z ≠ Z)
    (U : Set X) (hτU : τ '' U = U) (p : X)
    (hU₁ : Z₁ ∩ U = connectedComponentIn U p) (hU₂ : Z₂ ∩ U = U \ connectedComponentIn U p) :
    ∀ y ∈ connectedComponentIn U p, τ y ∈ U \ connectedComponentIn U p := by p2m_exact_reverting @_root_.P2MW.S_image_connectedComponentIn_subset_diff_of_forall_mem_irreducibleComponents_image_ne.solution
