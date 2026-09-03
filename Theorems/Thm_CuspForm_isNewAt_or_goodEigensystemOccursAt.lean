import Mathlib
import Definitions.Def_CuspForm_Newforms
import P2M.Util
import P2M.Sol.S_CuspForm_isNewAt_or_goodEigensystemOccursAt
attribute [-simp] ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_traceLin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply

theorem CuspForm.isNewAt_or_goodEigensystemOccursAt {N q : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 (N * q)) 2) (hf : f.IsNormalizedEigenform) (hq : q.Prime) (hqN : ¬ q ∣ N) : f.IsNewAt q ∨ f.GoodEigensystemOccursAt N := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_isNewAt_or_goodEigensystemOccursAt.solution
