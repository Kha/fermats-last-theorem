import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply

set_option autoImplicit false

theorem CuspForm.IsNormalizedEigenform.exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hf : f.IsNormalizedEigenform)
    (α : ℕ → ℂ)
    (hα : ∀ q : ℕ, q.Prime → q ∣ N → ¬ q ∣ M → ¬ q ^ 2 ∣ N →
      α q ^ 2 - ModularFormClass.qCoeff f q * α q + q = 0) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2, g.IsNormalizedEigenform ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff f ℓ) ∧
      (∀ q : ℕ, q.Prime → q ∣ N → N.factorization q = M.factorization q →
        ModularFormClass.qCoeff g q = ModularFormClass.qCoeff f q) ∧
      (∀ q : ℕ, q.Prime → q ∣ N → ¬ q ∣ M → ¬ q ^ 2 ∣ N →
        ModularFormClass.qCoeff g q = α q) ∧
      (∀ q : ℕ, q.Prime → q ^ 2 ∣ N → M.factorization q < N.factorization q →
        ModularFormClass.qCoeff g q = 0) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root.solution
