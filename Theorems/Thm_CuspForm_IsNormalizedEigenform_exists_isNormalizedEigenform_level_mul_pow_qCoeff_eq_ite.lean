import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_level_mul_pow_qCoeff_eq_ite
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply

set_option autoImplicit false

theorem CuspForm.IsNormalizedEigenform.exists_isNormalizedEigenform_level_mul_pow_qCoeff_eq_ite
    {M : ℕ} [NeZero M] {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hf : f.IsNormalizedEigenform) {q : ℕ} (hq : q.Prime) (e : ℕ) (he : 1 ≤ e)
    (he2 : ¬ q ∣ M → 2 ≤ e) [NeZero (M * q ^ e)] :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 (M * q ^ e)) 2, g.IsNormalizedEigenform ∧
      ∀ n : ℕ, ModularFormClass.qCoeff g n =
        if q ∣ n then 0 else ModularFormClass.qCoeff f n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_level_mul_pow_qCoeff_eq_ite.solution
