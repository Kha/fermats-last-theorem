import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_coprime_of_forall_prime_not_dvd

theorem CuspForm.IsNormalizedEigenform.qCoeff_eq_of_coprime_of_forall_prime_not_dvd
    {M R R' : ℕ}
    {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2}
    {g' : CuspForm (CongruenceSubgroup.Gamma0 R') 2}
    (hg : CuspForm.IsNormalizedEigenform g) (hg' : CuspForm.IsNormalizedEigenform g')
    (hR : R ∣ M) (hR' : R' ∣ M)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
      ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff g' ℓ)
    {n : ℕ} (hn : Nat.Coprime n M) :
    ModularFormClass.qCoeff g n = ModularFormClass.qCoeff g' n := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_coprime_of_forall_prime_not_dvd.solution
