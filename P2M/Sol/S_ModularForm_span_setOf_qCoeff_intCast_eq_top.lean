import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_X1
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gammaH
import P2M.Util
namespace P2MW.S_ModularForm_span_setOf_qCoeff_intCast_eq_top
attribute [-instance] TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq
attribute [-simp] CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

set_option autoImplicit false

p2m_open_scoped "MatrixGroups ModularForm P2MW.S_ModularForm_span_setOf_qCoeff_intCast_eq_top.ModularForm"

namespace ModularForm p2m_export "ModularForm" "IsGLPos.coe_smul coeHom coe_smul" end ModularForm
p2m_open_scoped "ModularForm" in

theorem ModularForm.span_setOf_qCoeff_intCast_eq_top_of_gammaH_top_eq (N : ℕ) [NeZero N] (k : ℤ)
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CohCarrier.GammaH N ⊤ = Γ) :
    Submodule.span ℂ {f : ModularForm Γ k |
        ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)} = ⊤ := by
  subst hΓ
  rw [eq_top_iff]
  rintro F -
  obtain ⟨n, c, G, r, hG, hF⟩ := ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gammaH N ⊤ F
  have hFG : F = ∑ i, c i • G i := by
    apply DFunLike.coe_injective
    show ⇑F = ⇑(∑ i, c i • G i)
    rw [hF]
    change _ = FunLike.coeAddMonoidHom (ModularForm _ k) UpperHalfPlane ℂ (∑ i, c i • G i)
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ = ⇑(c i • G i)
    rw [ModularForm.IsGLPos.coe_smul]
  rw [hFG]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span fun m => ?_)
  exact ⟨PowerSeries.coeff m (r i), ((hG i).coeff m).symm⟩

theorem solution (N : ℕ) [NeZero N] (k : ℤ) :
    Submodule.span ℂ {f : ModularForm (CongruenceSubgroup.Gamma0 N) k |
        ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)} = ⊤ :=
  ModularForm.span_setOf_qCoeff_intCast_eq_top_of_gammaH_top_eq N k _ CohCarrier.GammaH_top
