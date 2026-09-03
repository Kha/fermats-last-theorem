import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_CuspForm_exists_cyclic_span_heckeAlgebra
import P2M.Util
namespace P2MW.S_CuspForm_exists_top_eq_heckeAlgebra_adjoin_smul
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

theorem solution (M : ℕ) [NeZero M] :
    ∃ f₀ : CuspForm (CongruenceSubgroup.Gamma0 M) 2,
      ∀ g : CuspForm (CongruenceSubgroup.Gamma0 M) 2,
        ∃ T : Algebra.adjoin ℂ
            ((CuspForm.heckeAlgebra M 2 ∅ : Set
              (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)))),
          (T : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) f₀ = g := by
  obtain ⟨f₀, hf₀⟩ := CuspForm.exists_cyclic_span_heckeAlgebra M
  refine ⟨f₀, fun g => ?_⟩
  obtain ⟨T, hTmem, hTg⟩ := hf₀ g

  exact ⟨⟨T, Algebra.span_le_adjoin ℂ _ hTmem⟩, hTg⟩
