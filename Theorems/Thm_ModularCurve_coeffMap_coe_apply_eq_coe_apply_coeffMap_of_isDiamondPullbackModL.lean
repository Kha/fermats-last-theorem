import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDiamondModL
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import P2M.Util
import P2M.Sol.S_ModularCurve_coeffMap_coe_apply_eq_coe_apply_coeffMap_of_isDiamondPullbackModL
attribute [-instance] CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

set_option autoImplicit false

open ModularCurve hiding exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
open scoped MatrixGroups

theorem ModularCurve.coeffMap_coe_apply_eq_coe_apply_coeffMap_of_isDiamondPullbackModL
    (k K : Type*) [Field k] [Field K] (j : k →+* K)
    (N : ℕ) [NeZero N] (hN : (N : k) ≠ 0) (H : Subgroup (ZMod N)ˣ)
    (ρk : CongruenceSubgroup.Gamma0 N →*
      (qExpFunctionFieldC k (CohCarrier.GammaH N H) ≃ₐ[k] qExpFunctionFieldC k (CohCarrier.GammaH N H)))
    (ρK : CongruenceSubgroup.Gamma0 N →*
      (qExpFunctionFieldC K (CohCarrier.GammaH N H) ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH N H)))
    (hρk : IsDiamondPullbackModL k N H ρk) (hρK : IsDiamondPullbackModL K N H ρK)
    (γ : CongruenceSubgroup.Gamma0 N) (x : qExpFunctionFieldC k (CohCarrier.GammaH N H)) :
    coeffMap j ((ρk γ x : qExpFunctionFieldC k (CohCarrier.GammaH N H)) : LaurentSeries k) =
      ((ρK γ ⟨coeffMap j (x : LaurentSeries k), coeffMap_mem_qExpFunctionFieldC_of_mem j (CohCarrier.GammaH N H) x.2⟩ :
          qExpFunctionFieldC K (CohCarrier.GammaH N H)) : LaurentSeries K) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffMap_coe_apply_eq_coe_apply_coeffMap_of_isDiamondPullbackModL.solution
