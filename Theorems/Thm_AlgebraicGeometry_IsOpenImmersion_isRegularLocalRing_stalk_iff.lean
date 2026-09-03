import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsOpenImmersion_isRegularLocalRing_stalk_iff

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsOpenImmersion.isRegularLocalRing_stalk_iff
    {U X : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (u : U) :
    IsRegularLocalRing (X.presheaf.stalk (i.base u)) ↔ IsRegularLocalRing (U.presheaf.stalk u) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsOpenImmersion_isRegularLocalRing_stalk_iff.solution
