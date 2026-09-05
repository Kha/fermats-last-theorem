module

public import Mathlib
public import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
public import Definitions.Def_ModularCurve_SpecializeModuli
public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
public import P2M.Util
public import P2M.Sol.S_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty

@[expose] public section
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve
theorem ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
    (k : Type*) [Field k] [DecidableEq (RatFunc k)] {q : ℕ} [Fact q.Prime] [CharP k q]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data) :
    frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k))
      = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty.solution
