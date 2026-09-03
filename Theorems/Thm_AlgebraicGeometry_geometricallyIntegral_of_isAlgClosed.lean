import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed

universe u
open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [LocallyOfFiniteType f] :
    GeometricallyIntegral f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed.solution
