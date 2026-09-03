import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsAffineOpen_isRegularLocalRing_stalk_of_isRegularRing

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsAffineOpen.isRegularLocalRing_stalk_of_isRegularRing
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (hreg : IsRegularRing Γ(X, U))
    (x : X) (hx : x ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsAffineOpen_isRegularLocalRing_stalk_of_isRegularRing.solution
