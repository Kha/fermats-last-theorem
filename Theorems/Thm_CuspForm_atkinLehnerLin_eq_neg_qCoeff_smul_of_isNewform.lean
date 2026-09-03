import Mathlib
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_AtkinLehnerOperator
import P2M.Util
import P2M.Sol.S_CuspForm_atkinLehnerLin_eq_neg_qCoeff_smul_of_isNewform
attribute [-simp] CuspForm.coe_traceLin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply

theorem CuspForm.atkinLehnerLin_eq_neg_qCoeff_smul_of_isNewform {N q : ℕ} [NeZero N]
    (W : ModularForm.AtkinLehnerDatum N q) (hq : q.Prime)
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNewform) :
    CuspForm.atkinLehnerLin W 2 f = (-ModularFormClass.qCoeff f q) • f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_atkinLehnerLin_eq_neg_qCoeff_smul_of_isNewform.solution
