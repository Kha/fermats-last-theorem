import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_isRegularRing_stalk_of_forall_isRegularLocalRing_stalk

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

theorem AlgebraicGeometry.Scheme.isRegularRing_stalk_of_forall_isRegularLocalRing_stalk
    {X : Scheme.{u}} (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) (x : X) :
    IsRegularRing (X.presheaf.stalk x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_isRegularRing_stalk_of_forall_isRegularLocalRing_stalk.solution
