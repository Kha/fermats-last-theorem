import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_specializes_isLocalization_atPrime_stalk

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_specializes_isLocalization_atPrime_stalk
    {X : Scheme.{u}} (y : X) (P : Ideal (X.presheaf.stalk y)) [P.IsPrime] :
    ∃ (x : X) (h : x ⤳ y),
      letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
      IsLocalization.AtPrime (X.presheaf.stalk x) P := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_specializes_isLocalization_atPrime_stalk.solution
