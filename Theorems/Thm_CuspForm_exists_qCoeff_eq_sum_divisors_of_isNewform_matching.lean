import Definitions.Def_CuspForm_Newforms
import P2M.Util
import P2M.Sol.S_CuspForm_exists_qCoeff_eq_sum_divisors_of_isNewform_matching
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply

set_option autoImplicit false
theorem CuspForm.exists_qCoeff_eq_sum_divisors_of_isNewform_matching
    (M N : ℕ) [NeZero N] (hMN : M ∣ N)
    (f₀ : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf₀ : f₀.IsNewform)
    (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hg : g.IsNormalizedEigenform)
    (hmatch : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N →
      ModularFormClass.qCoeff f₀ ℓ = ModularFormClass.qCoeff g ℓ) :
    ∃ c : ℕ → ℂ, ∀ n : ℕ, ModularFormClass.qCoeff g n =
      ∑ d ∈ (N / M).divisors, c d * (if d ∣ n then ModularFormClass.qCoeff f₀ (n / d) else 0) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_qCoeff_eq_sum_divisors_of_isNewform_matching.solution
