import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_norm_lt_of_heckeTLin_eq_smul
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero

theorem CuspForm.norm_lt_of_heckeTLin_eq_smul
    {N : ℕ} {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f ≠ 0)
    {q : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N) {a : ℂ}
    (ha : CuspForm.heckeTLin 2 hq hqN f = a • f) :
    ‖a‖ < q + 1 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_norm_lt_of_heckeTLin_eq_smul.solution
