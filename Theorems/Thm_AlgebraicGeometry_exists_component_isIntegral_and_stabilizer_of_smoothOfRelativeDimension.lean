import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_component_isIntegral_and_stabilizer_of_smoothOfRelativeDimension

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_component_isIntegral_and_stabilizer_of_smoothOfRelativeDimension
    {k : Type u} [Field k] (M : Scheme.{u}) (πM : M ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n πM]
    (x : M) (G : Type u) [Group G] (ρ : G →* Aut M) :
    ∃ (C₀ : M.Opens) (G₀ : Subgroup G),
      IsClosed (C₀ : Set M) ∧ _root_.IsConnected (C₀ : Set M) ∧ x ∈ C₀ ∧ IsIntegral (C₀ : Scheme.{u}) ∧
      (∀ g : G, g ∈ G₀ ↔ (ρ g).hom ⁻¹ᵁ C₀ = C₀) ∧
      (∀ g : G, (ρ g).hom.base x ∈ C₀ → g ∈ G₀) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_component_isIntegral_and_stabilizer_of_smoothOfRelativeDimension.solution
