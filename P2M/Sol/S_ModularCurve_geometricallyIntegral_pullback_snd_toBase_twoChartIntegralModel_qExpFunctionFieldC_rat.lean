import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charZero
import P2M.Util
namespace P2MW.S_ModularCurve_geometricallyIntegral_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_rat
attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul

set_option autoImplicit false

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [Fact p.Prime]
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] :
    GeometricallyIntegral
      (pullback.snd (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
        (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) := by
  rw [geometricallyIntegral_iff, geometrically_iff_of_commRing (R := ℚ)]
  intro K _ _ Y fst snd h

  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  letI : Algebra ↥(GaloisRep.ratLocalizedAt p) K := ((algebraMap ℚ K).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)).toAlgebra

  have big := h.paste_horiz (IsPullback.of_hasPullback
    (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
    (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at big
  have e : (algebraMap ℚ K).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) = algebraMap ↥(GaloisRep.ratLocalizedAt p) K := rfl
  rw [e] at big
  haveI : IsIntegral ↑(pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) K)))) :=
    ModularCurve.isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charZero Γ p j K
  haveI : Nonempty ↥Y := (inferInstance : Nonempty ↥(pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) K))))).map big.isoPullback.inv.base
  exact isIntegral_of_isOpenImmersion big.isoPullback.hom
