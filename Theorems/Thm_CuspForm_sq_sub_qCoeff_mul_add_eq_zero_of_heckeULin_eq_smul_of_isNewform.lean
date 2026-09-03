import Definitions.Def_CuspForm_Newforms
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply

set_option autoImplicit false

theorem CuspForm.sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform
    (N r : ℕ) [NeZero N] (hr : r.Prime) (hrN : ¬ r ∣ N) (S : Finset ℕ)
    (M₀ : ℕ) (hM₀N : M₀ ∣ N)
    (g₀ : CuspForm (CongruenceSubgroup.Gamma0 M₀) 2) (hg₀ : g₀.IsNewform)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (N * r)) 2) (hf : f ≠ 0)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓNr : ¬ ℓ ∣ N * r), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓNr f = ModularFormClass.qCoeff g₀ ℓ • f)
    (u : ℂ)
    (hu : haveI : NeZero (N * r) := ⟨mul_ne_zero (NeZero.ne N) hr.ne_zero⟩
      CuspForm.heckeULin 2 (dvd_mul_left r N) f = u • f) :
    u ^ 2 - ModularFormClass.qCoeff g₀ r * u + r = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform.solution
