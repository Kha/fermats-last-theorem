import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_exists_stabilization_qCoeff_eq
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat

theorem CuspForm.IsNormalizedEigenform.exists_stabilization_qCoeff_eq
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hg : g.IsNormalizedEigenform) (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M)
    (ε : ℂ) (hε : ε ^ 2 - ModularFormClass.qCoeff g p * ε + p = 0) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 (M * p)) 2, f.IsNormalizedEigenform ∧
      (∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) ∧
      ModularFormClass.qCoeff f p = ε := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_exists_stabilization_qCoeff_eq.solution
