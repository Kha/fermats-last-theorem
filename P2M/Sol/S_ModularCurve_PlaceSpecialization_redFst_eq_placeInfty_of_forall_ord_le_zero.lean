module

public import Mathlib
public import Definitions.Def_ModularCurve_LevelOneGlueData
public import Definitions.Def_ModularCurve_SpecializeModuli
public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
public import Theorems.Thm_ModularCurve_PlaceSpecialization_sp_eq_placeInfty_of_forall_ord_le_zero
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing ModularCurve

theorem solution
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
    P.redFst W = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k) := by

  suffices key : (letI := Classical.decEq (RatFunc k);
      P.redFst W = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k)) by
    convert key
  have hj : heckeAlphaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) :=
    Subtype.ext (coe_heckeAlphaBar 1 q _)
  refine P.sp_eq_placeInfty_of_forall_ord_le_zero _ fun b => ?_
  have h := hW b
  rw [← hj, ← (heckeAlphaBar (AlgebraicClosure ℚ) 1 q).commutes (b : AlgebraicClosure ℚ),
    ← map_sub, Place.ord_restrictAlong _ hα] at h
  have hepos : 0 < (Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) W : ℤ) := by
    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q)
    haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) 1 q)
    haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα
    exact_mod_cast Place.ramificationIndex_pos (F := modularFunctionFieldBar 1) W
  by_contra hpos
  push_neg at hpos
  exact absurd h (not_le.mpr (mul_pos hepos hpos))
