import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_ModularForm_exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le
set_option autoImplicit false

theorem ModularForm.exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] :
    ∃ (A : ModularForm (CongruenceSubgroup.Gamma0 N') ((p : ℤ) - 1)) (b : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff A n = (b n : ℂ)) ∧ (p : ℤ) ∣ b 0 - 1 ∧ ∀ n, 0 < n → (p : ℤ) ∣ b n := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le.solution
