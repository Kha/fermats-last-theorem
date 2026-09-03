import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_of_flat_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isReduced_of_flat_of_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [IsReduced X] : IsReduced Y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_of_flat_of_surjective.solution
