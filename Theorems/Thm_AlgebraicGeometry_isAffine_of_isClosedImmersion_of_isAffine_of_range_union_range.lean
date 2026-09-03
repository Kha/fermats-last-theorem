import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isAffine_of_range_union_range

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isAffine_of_isClosedImmersion_of_isAffine_of_range_union_range
    (X Z₁ Z₂ : Scheme.{0}) (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    (h₁ : IsClosedImmersion i₁) (h₂ : IsClosedImmersion i₂)
    (hZ₁ : IsAffine Z₁) (hZ₂ : IsAffine Z₂)
    (hred : IsReduced X)
    (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) :
    IsAffine X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isAffine_of_range_union_range.solution
