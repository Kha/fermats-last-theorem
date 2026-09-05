module

public import Mathlib
public import Definitions.Def_ModularCurve_PlaceSpecialization
public import Definitions.Def_ModularCurve_SpecializeModuli
public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
public import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_PlaceSpecialization_sp_eq_charLGeomPlaceOfPoint_of_ord_pos
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
open AlgebraicCurve IsLocalRing ModularCurve

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 1)) (b : A)
    (hv : 0 < v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) (b : AlgebraicClosure ℚ))) :
    P.sp v = charLGeomPlaceOfPoint k (red b) :=
  ModularCurve.eq_charLGeomPlaceOfPoint_of_ord_pos (P.d0_j v b hv)
