import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_forall_prime_qCoeff_eq

open ModularFormClass
theorem CuspForm.IsNormalizedEigenform.qCoeff_eq_of_forall_prime_qCoeff_eq {N : ℕ}
    {f g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform)
    (hg : g.IsNormalizedEigenform)
    (h : ∀ p : ℕ, p.Prime → qCoeff f p = qCoeff g p) (n : ℕ) :
    qCoeff f n = qCoeff g n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_forall_prime_qCoeff_eq.solution
