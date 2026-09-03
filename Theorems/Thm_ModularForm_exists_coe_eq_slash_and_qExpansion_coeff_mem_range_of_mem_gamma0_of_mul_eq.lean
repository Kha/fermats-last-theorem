import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularForm_exists_coe_eq_slash_and_qExpansion_coeff_mem_range_of_mem_gamma0_of_mul_eq
attribute [-instance] CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex WeierstrassCurve.Affine.Point.instFinite TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq
attribute [-simp] CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_coe_eq_slash_and_qExpansion_coeff_mem_range_of_mem_gamma0_of_mul_eq
    (N' p M : ℕ) [NeZero N'] [NeZero M] [Fact p.Prime] (hM : N' * p = M) (k : ℤ)
    (ι : AlgebraicClosure ℚ →+* ℂ)
    (f : ModularForm ((CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * p) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑f) ∈ Set.range ι)
    (γ' : SL(2, ℤ)) (hγ' : γ' ∈ CongruenceSubgroup.Gamma0 N')
    (h : GL (Fin 2) ℝ)
    (hh : (h : Matrix (Fin 2) (Fin 2) ℝ) =
      !![((γ' 0 0 : ℤ) : ℝ), ((γ' 0 1 : ℤ) : ℝ) / (p : ℝ); (p : ℝ) * ((γ' 1 0 : ℤ) : ℝ), ((γ' 1 1 : ℤ) : ℝ)]) :
    ∃ f' : ModularForm ((CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * p) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑f' = (⇑f : UpperHalfPlane → ℂ) ∣[k] h) ∧
      ∀ n : ℕ, (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑f') ∈ Set.range ι := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_coe_eq_slash_and_qExpansion_coeff_mem_range_of_mem_gamma0_of_mul_eq.solution
