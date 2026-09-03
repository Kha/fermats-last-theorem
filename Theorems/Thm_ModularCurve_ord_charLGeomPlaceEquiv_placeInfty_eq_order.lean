import Mathlib
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import P2M.Util
import P2M.Sol.S_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_eq_order
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

open AlgebraicCurve ModularCurve
theorem ModularCurve.ord_charLGeomPlaceEquiv_placeInfty_eq_order (k : Type*) [Field k] [DecidableEq (RatFunc k)]
    (g : ↥(modularFunctionFieldC k 1)) :
    (charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k)).ord g
      = (g : LaurentSeries k).order := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_eq_order.solution
