import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_SpecializeModuli
import Theorems.Thm_ModularCurve_smul_charLGeomPlaceOfPoint_of_smul_jqModC
import P2M.Util
namespace P2MW.S_ModularCurve_arithFrobC_smul_charLGeomPlaceOfPoint
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

open AlgebraicCurve ModularCurve

theorem solution
    (q : ℕ) {K : Type*} [Field K] [Fact q.Prime] [CharP K q] [PerfectField K] (a : K) :
    ModularCurve.arithFrobC q K 1 • ModularCurve.charLGeomPlaceOfPoint K a
      = ModularCurve.charLGeomPlaceOfPoint K (a ^ q) :=

  ModularCurve.smul_charLGeomPlaceOfPoint_of_smul_jqModC (ModularCurve.arithFrobC q K 1)
    (ModularCurve.arithFrobC_smul_jq q K 1) a
