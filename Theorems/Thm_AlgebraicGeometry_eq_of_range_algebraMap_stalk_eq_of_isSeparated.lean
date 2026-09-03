import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_eq_of_range_algebraMap_stalk_eq_of_isSeparated

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.eq_of_range_algebraMap_stalk_eq_of_isSeparated
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated] (x y : X)
    (h : (algebraMap (X.presheaf.stalk x) X.functionField).range =
      (algebraMap (X.presheaf.stalk y) X.functionField).range) :
    x = y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_eq_of_range_algebraMap_stalk_eq_of_isSeparated.solution
