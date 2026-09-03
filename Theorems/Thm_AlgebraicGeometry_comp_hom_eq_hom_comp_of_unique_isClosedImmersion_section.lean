import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_comp_hom_eq_hom_comp_of_unique_isClosedImmersion_section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.comp_hom_eq_hom_comp_of_unique_isClosedImmersion_section
    {X Y : Scheme.{u}} (π : X ⟶ Y) (c : Y ⟶ X) [IsClosedImmersion c] (hcπ : c ≫ π = 𝟙 Y)
    (huniq : ∀ s : Y ⟶ X, IsClosedImmersion s → s ≫ π = 𝟙 Y → s = c)
    (φ : X ≅ X) (φ₀ : Y ≅ Y) (hπ : φ.hom ≫ π = π ≫ φ₀.hom) :
    c ≫ φ.hom = φ₀.hom ≫ c := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_comp_hom_eq_hom_comp_of_unique_isClosedImmersion_section.solution
