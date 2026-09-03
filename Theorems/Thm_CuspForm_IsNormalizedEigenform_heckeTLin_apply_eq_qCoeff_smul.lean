import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul

theorem CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hf : f.IsNormalizedEigenform)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    CuspForm.heckeTLin 2 hℓ hℓN f = ModularFormClass.qCoeff f ℓ • f := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul.solution
