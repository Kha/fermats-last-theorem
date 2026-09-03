import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsAffineOpen_range_algebraMap_functionField_eq_iInf

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsAffineOpen.range_algebraMap_functionField_eq_iInf
    {X : Scheme.{u}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    (algebraMap Γ(X, U) X.functionField).range =
      ⨅ (x : X) (_ : x ∈ U), (algebraMap (X.presheaf.stalk x) X.functionField).range := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsAffineOpen_range_algebraMap_functionField_eq_iInf.solution
