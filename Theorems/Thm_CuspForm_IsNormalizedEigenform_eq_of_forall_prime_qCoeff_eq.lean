import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_eq_of_forall_prime_qCoeff_eq
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularFormClass
theorem CuspForm.IsNormalizedEigenform.eq_of_forall_prime_qCoeff_eq {N : ℕ}
    {f g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform)
    (hg : g.IsNormalizedEigenform)
    (h : ∀ p : ℕ, p.Prime → qCoeff f p = qCoeff g p) : f = g := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_eq_of_forall_prime_qCoeff_eq.solution
