import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_smoothOfRelativeDimension_of_irreducibleSpace

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.smoothOfRelativeDimension_of_irreducibleSpace
    (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X] [Smooth f]
    (V : X.Opens) (hV : (V : Set X).Nonempty) [SmoothOfRelativeDimension n (V.ι ≫ f)] :
    SmoothOfRelativeDimension n f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_of_irreducibleSpace.solution
