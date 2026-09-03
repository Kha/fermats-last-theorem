import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_app_injective_and_range_eq_invariants_of_isBasis

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.app_injective_and_range_eq_invariants_of_isBasis
    {M X : Scheme.{0}} (π : M ⟶ X)
    {H : Type} [Group H] (ρ : H →* Aut M) (hπ : ∀ h : H, (ρ h).hom ≫ π = π)
    (B : Set X.Opens) (hB : TopologicalSpace.Opens.IsBasis B)
    (hsecB : ∀ W ∈ B, Function.Injective (π.app W))
    (hinvB : ∀ W ∈ B, Set.range (π.app W) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ W) (π ⁻¹ᵁ W) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s}) :
    (∀ V : X.Opens, Function.Injective (π.app V)) ∧
    (∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ h : H, (ρ h).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ h]) s = s}) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_app_injective_and_range_eq_invariants_of_isBasis.solution
