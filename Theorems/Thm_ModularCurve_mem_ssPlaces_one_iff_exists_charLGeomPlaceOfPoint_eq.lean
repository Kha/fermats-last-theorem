import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SpecializeModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open AlgebraicCurve

theorem ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
    (q : ℕ) (K : Type*) [Field K] [DecidableEq K] (w : Place K (modularFunctionFieldC K 1)) :
    w ∈ ssPlaces q 1 K ↔ ∃ a ∈ ssJSet q K, charLGeomPlaceOfPoint K a = w := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq.solution
