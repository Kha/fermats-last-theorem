import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_ModularForm_alSlash_add_heckeU_alSlash_alSlash

theorem ModularForm.alSlash_add_heckeU_alSlash_alSlash {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map k γ f = f) :
    ModularForm.alSlash W k f + ModularForm.heckeU k q (ModularForm.alSlash W k (ModularForm.alSlash W k f))
      = ModularForm.alSlash W k f + ((q : ℂ) ^ (k - 2)) • ModularForm.heckeU k q f := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_alSlash_add_heckeU_alSlash_alSlash.solution
