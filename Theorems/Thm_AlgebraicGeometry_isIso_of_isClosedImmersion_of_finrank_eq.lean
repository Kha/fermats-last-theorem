import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isClosedImmersion_of_finrank_eq
    {X Y Z : Scheme.{u}} (fX : X ⟶ Z) (fY : Y ⟶ Z) (i : X ⟶ Y) (hi : i ≫ fY = fX)
    [IsClosedImmersion i]
    [IsFinite fX] [Flat fX] [LocallyOfFinitePresentation fX]
    [IsFinite fY] [Flat fY] [LocallyOfFinitePresentation fY]
    (hrank : ∀ z : Z, fX.finrank z = fY.finrank z) :
    IsIso i := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_eq.solution
