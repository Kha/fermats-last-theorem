module

public import Mathlib
public import Definitions.Def_ModularCurve_LevelOneGlueData
public import Definitions.Def_ModularCurve_SpecializeModuli
public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero

@[expose] public section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve
theorem ModularCurve.PlaceSpecialization.redFst_eq_placeInfty_of_forall_ord_le_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq (RatFunc k)] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hW : ∀ a : A, W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)) ≤ 0) :
    P.redFst W = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero.solution
