import Definitions.Def_CuspForm_Newforms
import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_IsNewform_sum_range_slash_heckeDiagMatrix_conj_eq_qCoeff_smul
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CuspForm.coe_heckeULowerLin_apply

open scoped ModularForm MatrixGroups in
theorem CuspForm.IsNewform.sum_range_slash_heckeDiagMatrix_conj_eq_qCoeff_smul
    {N N₀ q : ℕ} {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : CuspForm.IsNewform f)
    (hq : q.Prime) (hqN : q * N₀ = N) (hqN₀ : ¬ q ∣ N₀) :
    ∑ j ∈ Finset.range q,
      (⇑f ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q)
        ∣[(2 : ℤ)] (ModularGroup.S * ModularGroup.T ^ (-((N * j : ℕ) : ℤ)) * ModularGroup.S⁻¹)
      = (ModularFormClass.qCoeff f q) • ⇑f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNewform_sum_range_slash_heckeDiagMatrix_conj_eq_qCoeff_smul.solution
