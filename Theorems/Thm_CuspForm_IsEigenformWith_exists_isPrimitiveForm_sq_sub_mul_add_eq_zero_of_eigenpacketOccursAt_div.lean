import Definitions.Def_CuspForm_PrimitiveFormGamma1
import P2M.Util
import P2M.Sol.S_CuspForm_IsEigenformWith_exists_isPrimitiveForm_sq_sub_mul_add_eq_zero_of_eigenpacketOccursAt_div
attribute [-instance] FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.PeterssonCoset.mapGL_apply

set_option autoImplicit false

theorem CuspForm.IsEigenformWith.exists_isPrimitiveForm_sq_sub_mul_add_eq_zero_of_eigenpacketOccursAt_div
    {M : ℕ} [NeZero M] {k : ℤ} {ε : DirichletCharacter ℂ M}
    {h : CuspForm (CongruenceSubgroup.Gamma1 M) k} (hh : CuspForm.IsEigenformWith ε h)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ M)
    (hold : CuspForm.EigenpacketOccursAt k (fun n => ModularFormClass.qCoeff h n)
      (fun n => ε (n : ZMod M)) (M / q)) :
    ∃ (Mg : ℕ) (_ : NeZero Mg) (εg : DirichletCharacter ℂ Mg)
      (g : CuspForm (CongruenceSubgroup.Gamma1 Mg) k) (hMg : Mg ∣ M / q),
      CuspForm.IsPrimitiveForm εg g ∧
      DirichletCharacter.changeLevel (hMg.trans (Nat.div_dvd_of_dvd hqM)) εg = ε ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff h ℓ) ∧
      ModularFormClass.qCoeff h q ^ 2 - ModularFormClass.qCoeff g q * ModularFormClass.qCoeff h q +
        εg (q : ZMod Mg) * (q : ℂ) ^ (k - 1) = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsEigenformWith_exists_isPrimitiveForm_sq_sub_mul_add_eq_zero_of_eigenpacketOccursAt_div.solution
