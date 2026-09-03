import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_of_etale
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isReduced_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [IsReduced Y] [IsLocallyNoetherian Y] :
    IsReduced X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_of_etale.solution
