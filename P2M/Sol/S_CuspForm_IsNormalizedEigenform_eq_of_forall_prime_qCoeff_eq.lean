import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_forall_prime_qCoeff_eq
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import P2M.Util
namespace P2MW.S_CuspForm_IsNormalizedEigenform_eq_of_forall_prime_qCoeff_eq

open ModularFormClass

theorem solution {N : ℕ}
    {f g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform)
    (hg : g.IsNormalizedEigenform)
    (h : ∀ p : ℕ, p.Prime → qCoeff f p = qCoeff g p) : f = g :=
  ModularFormClass.eq_of_forall_qCoeff_eq
    (by rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples 1)
    (CuspForm.IsNormalizedEigenform.qCoeff_eq_of_forall_prime_qCoeff_eq hf hg h)
