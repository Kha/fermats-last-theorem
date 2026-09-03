import Mathlib
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_comp_eq
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X Y Z : Scheme.{u}} (fX : X ⟶ Z) (fY : Y ⟶ Z) (i : X ⟶ Y) (hi : i ≫ fY = fX)
    [IsClosedImmersion i]
    [IsFinite fX] [Flat fX] [LocallyOfFinitePresentation fX]
    [IsFinite fY] [Flat fY] [LocallyOfFinitePresentation fY]
    (hrank : ∀ z : Z, fX.finrank z = fY.finrank z) :
    IsIso i := by
  exact AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_comp_eq i fY fX hi hrank
