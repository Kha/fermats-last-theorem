import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_locallyOfFinitePresentation_diagonal_of_locallyOfFiniteType

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.locallyOfFinitePresentation_diagonal_of_locallyOfFiniteType
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation (pullback.diagonal f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_locallyOfFinitePresentation_diagonal_of_locallyOfFiniteType.solution
