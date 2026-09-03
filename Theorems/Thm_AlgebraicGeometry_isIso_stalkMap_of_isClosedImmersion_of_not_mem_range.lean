import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_stalkMap_of_isClosedImmersion_of_not_mem_range

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_stalkMap_of_isClosedImmersion_of_not_mem_range
    {Z M₁ M₂ : Scheme.{u}} [IsReduced Z]
    (i₁ : M₁ ⟶ Z) (i₂ : M₂ ⟶ Z) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : ∀ z : Z, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (y : M₁) (hy : i₁.base y ∉ Set.range i₂.base) :
    IsIso (i₁.stalkMap y) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_stalkMap_of_isClosedImmersion_of_not_mem_range.solution
