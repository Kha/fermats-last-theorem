import Mathlib
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_eq_order
import Theorems.Thm_ModularCurve_order_jqModC
import P2M.Util
namespace P2MW.S_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_jqModC
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

set_option autoImplicit false

open AlgebraicCurve ModularCurve

set_option maxHeartbeats 1600000 in
theorem solution (k : Type*) [Field k] [DecidableEq (RatFunc k)] :
    (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord
        ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))) = -1 := by
  rw [ord_charLGeomPlaceEquiv_placeInfty_eq_order]
  exact order_jqModC k
