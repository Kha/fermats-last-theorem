module

public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty
import P2M.Util

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap

open AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem solution {K : Type*} [Field K] [DecidableEq (RatFunc K)] {q : Polynomial K} (hq : q ≠ 0) : (placeInfty K).ord (algebraMap (Polynomial K) (RatFunc K) q) = -(q.natDegree : ℤ) := by
  rw [AlgebraicCurve.RationalFunctionField.ord_placeInfty (RatFunc.algebraMap_ne_zero hq), RatFunc.intDegree_polynomial]
end S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
end P2MW

public section
open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem AlgebraicCurve.RationalFunctionField.ord_placeInfty_algebraMap {K : Type*} [Field K] [DecidableEq (RatFunc K)] {q : Polynomial K} (hq : q ≠ 0) : (placeInfty K).ord (algebraMap (Polynomial K) (RatFunc K) q) = -(q.natDegree : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap.solution
end
