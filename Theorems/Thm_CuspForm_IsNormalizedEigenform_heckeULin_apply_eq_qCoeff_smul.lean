import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_heckeULin_apply_eq_qCoeff_smul

theorem CuspForm.IsNormalizedEigenform.heckeULin_apply_eq_qCoeff_smul (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hf : f.IsNormalizedEigenform)
    (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) :
    CuspForm.heckeULin 2 hqN f = ModularFormClass.qCoeff f q • f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_heckeULin_apply_eq_qCoeff_smul.solution
