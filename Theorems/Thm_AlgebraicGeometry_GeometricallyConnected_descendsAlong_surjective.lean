import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective

universe u

open CategoryTheory MorphismProperty AlgebraicGeometry

theorem AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective :
    DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u}) @Surjective := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.solution
