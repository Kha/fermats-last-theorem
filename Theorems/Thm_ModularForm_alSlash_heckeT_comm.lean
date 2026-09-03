import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_ModularForm_alSlash_heckeT_comm

theorem ModularForm.alSlash_heckeT_comm {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    {f : UpperHalfPlane → ℂ} (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map k γ f = f) :
    ModularForm.alSlash W k (ModularForm.heckeT k ℓ f) = ModularForm.heckeT k ℓ (ModularForm.alSlash W k f) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_alSlash_heckeT_comm.solution
