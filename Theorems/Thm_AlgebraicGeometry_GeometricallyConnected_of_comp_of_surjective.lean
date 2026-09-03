import Mathlib.AlgebraicGeometry.Geometrically.Connected
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_GeometricallyConnected_of_comp_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.GeometricallyConnected.of_comp_of_surjective {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyConnected (f ≫ g)] [Surjective f] :
    GeometricallyConnected g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_GeometricallyConnected_of_comp_of_surjective.solution
