import Mathlib
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import P2M.Util
import P2M.Sol.S_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_jqModC
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.ord_charLGeomPlaceEquiv_placeInfty_jqModC (k : Type*) [Field k] [DecidableEq (RatFunc k)] :
    (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord
        ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1))) = -1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_jqModC.solution
