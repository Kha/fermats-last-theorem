import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isAffine_of_isClosedImmersion_of_surjective
    {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i] [IsAffine X₀] :
    IsAffine X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective.solution
