import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_isLocalization_atPrime_stalk_of_specializes

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

theorem AlgebraicGeometry.Scheme.isLocalization_atPrime_stalk_of_specializes
    {X : Scheme.{u}} {x y : ↥X} (h : y ⤳ x) :
    letI : Algebra ↑(X.presheaf.stalk x) ↑(X.presheaf.stalk y) := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsLocalization.AtPrime ↑(X.presheaf.stalk y)
      (Ideal.comap (X.presheaf.stalkSpecializes h).hom (IsLocalRing.maximalIdeal ↑(X.presheaf.stalk y))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_isLocalization_atPrime_stalk_of_specializes.solution
