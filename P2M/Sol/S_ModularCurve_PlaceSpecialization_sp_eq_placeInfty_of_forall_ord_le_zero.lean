module

public import Mathlib
public import Definitions.Def_ModularCurve_PlaceSpecialization
public import Definitions.Def_ModularCurve_SpecializeModuli
public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
public import Theorems.Thm_ModularCurve_eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_PlaceSpecialization_sp_eq_placeInfty_of_forall_ord_le_zero
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
open AlgebraicCurve IsLocalRing ModularCurve

theorem solution
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
    P.sp v = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k) :=
  letI := Classical.decEq (RatFunc k)
  ModularCurve.eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg (P.d0_j_pole v hv)
