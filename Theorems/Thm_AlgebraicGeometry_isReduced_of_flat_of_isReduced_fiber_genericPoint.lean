import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_of_flat_of_isReduced_fiber_genericPoint

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry~isReduced_of_flat_of_isReduced_pullback_of_isFractionRing"

universe u

theorem AlgebraicGeometry.isReduced_of_flat_of_isReduced_fiber_genericPoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y] [Flat f]
    [IsReduced (f.fiber (genericPoint Y))] :
    IsReduced X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_of_flat_of_isReduced_fiber_genericPoint.solution
