import Definitions.Def_CuspForm_Newforms
import P2M.Util
import P2M.Sol.S_CuspForm_IsNewform_sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

open scoped ModularForm MatrixGroups in
theorem CuspForm.IsNewform.sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero
    {R R₀ q : ℕ} [NeZero R]
    {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2} (hg : CuspForm.IsNewform g)
    (hq : q.Prime) (hqR : q * R₀ = R) (hqR₀ : q ∣ R₀) :
    ∑ j ∈ Finset.range q,
      (⇑g) ∣[(2 : ℤ)] (ModularGroup.S * ModularGroup.T ^ (-((R₀ * j : ℕ) : ℤ)) * ModularGroup.S⁻¹)
        = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNewform_sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero.solution
