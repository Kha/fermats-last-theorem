module

public import Mathlib
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
public import Definitions.Def_AlgebraicCurve_RatFuncPlaces
public import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap

@[expose] public section

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem AlgebraicCurve.RationalFunctionField.ord_placeInfty_algebraMap {K : Type*} [Field K] [DecidableEq (RatFunc K)] {q : Polynomial K} (hq : q ≠ 0) : (placeInfty K).ord (algebraMap (Polynomial K) (RatFunc K) q) = -(q.natDegree : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap.solution
