import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_cuspZero_apply_eq_and_apply_div_pow_eq
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.qExpandAlgHomC_apply
attribute [-simp] WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply

open scoped MatrixGroups

theorem ModularCurve.exists_algHom_qExpFunctionFieldC_gammaH_cuspZero_apply_eq_and_apply_div_pow_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ] :
    ∃ Θ : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] LaurentSeries K,
      (∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
        (x : LaurentSeries K) = ModularCurve.jqModC K → Θ x = ModularCurve.jqNModC K M) ∧
      (∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
        (x : LaurentSeries K) = ModularCurve.jqNModC K M → Θ x = ModularCurve.jqModC K) ∧
      ∀ (k : ℤ) (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
        (pf : PowerSeries ℤ), ModularCurve.IsIntegralQExp f pf → ModularCurve.intSeriesC K pf ≠ 0 →
        ∃ y : LaurentSeries K, y ≠ 0 ∧
          ∀ (n : ℕ) (F : ModularForm 𝒮ℒ ((n : ℤ) * k)) (P : PowerSeries ℤ),
            ModularCurve.IsIntegralQExp F P →
            ∀ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
              (x : LaurentSeries K) =
                ModularCurve.intSeriesC K P / ModularCurve.intSeriesC K pf ^ n →
              Θ x = ModularCurve.qExpand K M (ModularCurve.intSeriesC K P) / y ^ n := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_cuspZero_apply_eq_and_apply_div_pow_eq.solution
