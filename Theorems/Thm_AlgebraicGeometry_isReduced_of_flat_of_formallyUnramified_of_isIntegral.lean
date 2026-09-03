import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_of_flat_of_formallyUnramified_of_isIntegral

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isReduced_of_flat_of_formallyUnramified_of_isIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [FormallyUnramified f] [LocallyOfFiniteType f] [IsIntegral Y] : IsReduced X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_of_flat_of_formallyUnramified_of_isIntegral.solution
