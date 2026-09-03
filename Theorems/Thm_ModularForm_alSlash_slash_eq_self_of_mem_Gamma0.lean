import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0

theorem ModularForm.alSlash_slash_eq_self_of_mem_Gamma0 {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map k γ f = f)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    SlashAction.map k γ (ModularForm.alSlash W k f) = ModularForm.alSlash W k f := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_alSlash_slash_eq_self_of_mem_Gamma0.solution
