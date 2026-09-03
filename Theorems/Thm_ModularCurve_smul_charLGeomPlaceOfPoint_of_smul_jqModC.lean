import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_smul_charLGeomPlaceOfPoint_of_smul_jqModC
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

open AlgebraicCurve ModularCurve
theorem ModularCurve.smul_charLGeomPlaceOfPoint_of_smul_jqModC {K : Type*} [Field K]
    (g : SemilinearAut K (modularFunctionFieldC K 1))
    (hg : g • (⟨jqModC K, jqModC_mem K 1⟩ : modularFunctionFieldC K 1)
      = ⟨jqModC K, jqModC_mem K 1⟩) (a : K) :
    g • charLGeomPlaceOfPoint K a = charLGeomPlaceOfPoint K (SemilinearAut.baseAut g a) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_smul_charLGeomPlaceOfPoint_of_smul_jqModC.solution
