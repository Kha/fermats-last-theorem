import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : X ⟶ Y) (w : h ≫ g = f)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [IsLocallyNoetherian S] :
    LocallyOfFinitePresentation h := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_locallyOfFinitePresentation_of_comp_eq_of_isLocallyNoetherian.solution
