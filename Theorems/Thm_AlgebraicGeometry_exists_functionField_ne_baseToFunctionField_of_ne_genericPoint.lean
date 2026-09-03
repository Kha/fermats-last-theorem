import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_functionField_ne_baseToFunctionField_of_ne_genericPoint

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.exists_functionField_ne_baseToFunctionField_of_ne_genericPoint
    {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (c : X ⟶ Spec (CommRingCat.of K))
    (x : X) (hx : x ≠ genericPoint X) :
    ∃ s : ↑X.functionField, ∀ a : K, s ≠ AlgebraicCurve.baseToFunctionField c a := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_functionField_ne_baseToFunctionField_of_ne_genericPoint.solution
