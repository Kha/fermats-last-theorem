import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_LocallyOfFinitePresentation_of_comp_of_isFinite_of_flat_of_surjective

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_of_isFinite_of_flat_of_surjective
    {X Y Z : Scheme.{u}} (p : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite p] [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
    [LocallyOfFinitePresentation (p ≫ g)] :
    LocallyOfFinitePresentation g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_LocallyOfFinitePresentation_of_comp_of_isFinite_of_flat_of_surjective.solution
