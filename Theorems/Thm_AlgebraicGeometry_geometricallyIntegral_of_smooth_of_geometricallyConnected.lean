import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_geometricallyIntegral_of_smooth_of_geometricallyConnected
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyConnected
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] :
    GeometricallyIntegral f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_smooth_of_geometricallyConnected.solution
