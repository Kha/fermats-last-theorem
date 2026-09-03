import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected

universe u

open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected {X Y : Scheme.{u}} (f : X ⟶ Y)
    [GeometricallyIrreducible f] : GeometricallyConnected f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected.solution
