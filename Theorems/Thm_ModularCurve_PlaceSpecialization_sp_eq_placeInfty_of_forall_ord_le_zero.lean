module

public import Mathlib
public import Definitions.Def_ModularCurve_PlaceSpecialization
public import Definitions.Def_ModularCurve_SpecializeModuli
public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_sp_eq_placeInfty_of_forall_ord_le_zero

@[expose] public section
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve IsLocalRing ModularCurve
theorem ModularCurve.PlaceSpecialization.sp_eq_placeInfty_of_forall_ord_le_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 1))
    (hv : ∀ b : A, v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) (b : AlgebraicClosure ℚ)) ≤ 0) :
    letI := Classical.decEq (RatFunc k)
    P.sp v = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_sp_eq_placeInfty_of_forall_ord_le_zero.solution
