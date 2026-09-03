import Mathlib
import Definitions.Def_CuspForm_Newforms
import P2M.Util
import P2M.Sol.S_CuspForm_qCoeff_eq_zero_of_isNewform_of_sq_dvd
attribute [-simp] CuspForm.coe_heckeULowerLin_apply ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularFormClass
theorem CuspForm.qCoeff_eq_zero_of_isNewform_of_sq_dvd {N : ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNewform)
    (q : ℕ) (hq : q.Prime) (hsq : q ^ 2 ∣ N) :
    qCoeff f q = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_qCoeff_eq_zero_of_isNewform_of_sq_dvd.solution
