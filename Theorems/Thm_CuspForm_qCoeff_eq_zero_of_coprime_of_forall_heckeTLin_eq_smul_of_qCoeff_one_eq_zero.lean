import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_CuspForm_qCoeff_eq_zero_of_coprime_of_forall_heckeTLin_eq_smul_of_qCoeff_one_eq_zero

theorem CuspForm.qCoeff_eq_zero_of_coprime_of_forall_heckeTLin_eq_smul_of_qCoeff_one_eq_zero
    {M : ℕ} [NeZero M] {v : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hv : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∃ c : ℂ,
      CuspForm.heckeTLin 2 hℓ hℓM v = c • v)
    (h1 : ModularFormClass.qCoeff v 1 = 0)
    {n : ℕ} (hn : Nat.Coprime n M) :
    ModularFormClass.qCoeff v n = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_qCoeff_eq_zero_of_coprime_of_forall_heckeTLin_eq_smul_of_qCoeff_one_eq_zero.solution
