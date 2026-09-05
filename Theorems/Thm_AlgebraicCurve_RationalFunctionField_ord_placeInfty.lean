module

public import Mathlib
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
public import Definitions.Def_AlgebraicCurve_RatFuncPlaces
public import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty

@[expose] public section
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem AlgebraicCurve.RationalFunctionField.ord_placeInfty {K : Type*} [Field K] [DecidableEq (RatFunc K)] {f : RatFunc K} (hf : f ≠ 0) : (placeInfty K).ord f = -f.intDegree := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_ord_placeInfty.solution
