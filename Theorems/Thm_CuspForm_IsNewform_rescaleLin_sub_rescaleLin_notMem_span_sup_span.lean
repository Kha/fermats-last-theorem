import Definitions.Def_CuspForm_Newforms
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import P2M.Util
import P2M.Sol.S_CuspForm_IsNewform_rescaleLin_sub_rescaleLin_notMem_span_sup_span
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply

theorem CuspForm.IsNewform.rescaleLin_sub_rescaleLin_notMem_span_sup_span
    {L L₁ q m e R R₁ R' R₁' : ℕ} [NeZero L] (hq : q.Prime)
    (hL : q ^ m * L₁ = L) (hqL₁ : ¬ q ∣ L₁)
    (hR : q ^ m * R₁ = R) (hqR₁ : ¬ q ∣ R₁)
    (hR' : q ^ e * R₁' = R') (hqR₁' : ¬ q ∣ R₁') (he : e < m)
    {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2} {g' : CuspForm (CongruenceSubgroup.Gamma0 R') 2}
    (hg : CuspForm.IsNewform g) (hg' : CuspForm.IsNewform g')
    (h1 : 1 * R ∣ L) (h1' : 1 * R' ∣ L) :
    FreyPackage.ModMCarrier.rescaleLin h1 2 g - FreyPackage.ModMCarrier.rescaleLin h1' 2 g' ∉
      Submodule.span ℂ {F : CuspForm (CongruenceSubgroup.Gamma0 L) 2 |
          ∃ (i : ℕ) (h : q ^ i * R' ∣ L), 1 ≤ i ∧ F = FreyPackage.ModMCarrier.rescaleLin h 2 g'}
        ⊔ Submodule.span ℂ {F : CuspForm (CongruenceSubgroup.Gamma0 L) 2 |
          ∃ (p N' : ℕ) (h : p * N' ∣ L) (x : CuspForm (CongruenceSubgroup.Gamma0 N') 2),
            p.Prime ∧ p ≠ q ∧ p * N' = L ∧ F = FreyPackage.ModMCarrier.rescaleLin h 2 x} := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNewform_rescaleLin_sub_rescaleLin_notMem_span_sup_span.solution
