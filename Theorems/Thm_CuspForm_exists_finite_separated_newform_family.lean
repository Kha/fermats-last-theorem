import Definitions.Def_CuspForm_Newforms
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import P2M.Util
import P2M.Sol.S_CuspForm_exists_finite_separated_newform_family
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply

theorem CuspForm.exists_finite_separated_newform_family (M : ℕ) [NeZero M] :
    ∃ (ι : Type) (_ : Fintype ι) (N : ι → ℕ) (hN : ∀ i, N i ∣ M)
      (g : ∀ i, CuspForm (CongruenceSubgroup.Gamma0 (N i)) 2),
      (∀ i, CuspForm.IsNewform (g i)) ∧
      Submodule.span ℂ {F : CuspForm (CongruenceSubgroup.Gamma0 M) 2 |
        ∃ (i : ι) (d : ℕ) (h : d * N i ∣ M), F = FreyPackage.ModMCarrier.rescaleLin h 2 (g i)} = ⊤ ∧
      (∀ i j, i ≠ j → ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ℓ ∣ M ∧
        ModularFormClass.qCoeff (g i) ℓ ≠ ModularFormClass.qCoeff (g j) ℓ) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_finite_separated_newform_family.solution
