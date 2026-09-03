import Mathlib
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ModularCurve_SpecializeModuli
import P2M.Util
import P2M.Sol.S_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve
theorem ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
    (k : Type*) [Field k] {q : ℕ} [Fact q.Prime] [CharP k q]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data) (a : k) :
    frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k a) = charLGeomPlaceOfPoint k (a ^ q) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint.solution
