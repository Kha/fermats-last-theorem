import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_iso_hom_comp_eq_comp_hom_of_comp_hom_eq_of_isClosedImmersion_of_forall_mem_range_or

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_iso_hom_comp_eq_comp_hom_of_comp_hom_eq_of_isClosedImmersion_of_forall_mem_range_or
    {X C₁ C₂ S : Scheme.{u}} (x : X ⟶ S) (c₂ : C₂ ⟶ S)
    (i₁ : C₁ ⟶ X) (i₂ : C₂ ⟶ X) (hi₂ : i₂ ≫ x = c₂)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsIntegral C₂]
    (hcover : ∀ z : X, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (w : X ≅ X) (hw : w.hom ≫ x = x) (hfix : i₁ ≫ w.hom = i₁) :
    ∃ α₂ : C₂ ≅ C₂, α₂.hom ≫ c₂ = c₂ ∧ α₂.hom ≫ i₂ = i₂ ≫ w.hom  := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_iso_hom_comp_eq_comp_hom_of_comp_hom_eq_of_isClosedImmersion_of_forall_mem_range_or.solution
