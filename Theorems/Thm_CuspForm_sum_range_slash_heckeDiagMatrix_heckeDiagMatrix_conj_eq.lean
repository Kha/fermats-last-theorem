import Definitions.Def_ModularForm_HeckeOperatorForms
import P2M.Util
import P2M.Sol.S_CuspForm_sum_range_slash_heckeDiagMatrix_heckeDiagMatrix_conj_eq
attribute [-simp] FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul

open scoped ModularForm MatrixGroups in
theorem CuspForm.sum_range_slash_heckeDiagMatrix_heckeDiagMatrix_conj_eq
    {N q : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hq : q.Prime) (hqN : ¬ q ∣ N) :
    ∑ j ∈ Finset.range q,
      ((⇑f ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q)
        ∣[(2 : ℤ)] (ModularGroup.S * ModularGroup.T ^ (-((q * N * j : ℕ) : ℤ)) * ModularGroup.S⁻¹)
      = (ModularForm.heckeT 2 q ⇑f) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q - ⇑f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_sum_range_slash_heckeDiagMatrix_heckeDiagMatrix_conj_eq.solution
