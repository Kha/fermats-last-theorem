import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType

set_option autoImplicit false

universe u

open CategoryTheory

theorem AlgebraicGeometry.locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (h : LocallyOfFinitePresentation (f ≫ g))
    (hg : LocallyOfFiniteType g) : LocallyOfFinitePresentation f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType.solution
