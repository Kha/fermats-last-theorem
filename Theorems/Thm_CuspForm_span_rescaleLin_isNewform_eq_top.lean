import Definitions.Def_CuspForm_Newforms
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import P2M.Util
import P2M.Sol.S_CuspForm_span_rescaleLin_isNewform_eq_top
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply

theorem CuspForm.span_rescaleLin_isNewform_eq_top (M : ℕ) [NeZero M] :
    Submodule.span ℂ
      {F : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
        ∃ (R d : ℕ) (hdRM : d * R ∣ M) (g : CuspForm (CongruenceSubgroup.Gamma0 R) 2),
          CuspForm.IsNewform g ∧ F = FreyPackage.ModMCarrier.rescaleLin hdRM 2 g} = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_span_rescaleLin_isNewform_eq_top.solution
