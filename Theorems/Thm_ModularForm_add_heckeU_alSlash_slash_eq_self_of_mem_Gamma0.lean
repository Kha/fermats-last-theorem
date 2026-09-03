import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0

theorem ModularForm.add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0 {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map (2 : ℤ) γ f = f)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.Gamma0 W.R : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    SlashAction.map (2 : ℤ) γ (f + ModularForm.heckeU 2 q (ModularForm.alSlash W 2 f))
      = f + ModularForm.heckeU 2 q (ModularForm.alSlash W 2 f) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.solution
