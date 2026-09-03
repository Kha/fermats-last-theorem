import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_ModularCurve_geometricallyIntegral_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_rat
attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois
attribute [-simp] ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve~isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charZero"
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.geometricallyIntegral_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_rat
    (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [Fact p.Prime]
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] :
    GeometricallyIntegral
      (pullback.snd (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
        (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_geometricallyIntegral_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_rat.solution
