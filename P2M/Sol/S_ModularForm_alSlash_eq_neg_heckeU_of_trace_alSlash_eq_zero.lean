import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularForm_alSlash_alSlash
import P2M.Util
namespace P2MW.S_ModularForm_alSlash_eq_neg_heckeU_of_trace_alSlash_eq_zero

set_option autoImplicit false

theorem solution (q : ℕ) {M : ℕ} [NeZero M]
    (A : ModularForm.AtkinLehnerDatum M q) (k : ℤ) (F : CuspForm (CongruenceSubgroup.Gamma0 M) k)
    (hTrW : ModularForm.alSlash A k ⇑F +
      (q : ℂ) ^ (2 - k) • ModularForm.heckeU k q (ModularForm.alSlash A k (ModularForm.alSlash A k ⇑F)) = 0) :
    ModularForm.alSlash A k ⇑F = - ModularForm.heckeU k q ⇑F := by
  have hF : ∀ γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map k γ (⇑F) = ⇑F :=
    fun γ hγ => SlashInvariantForm.slash_action_eqn F γ hγ
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (ModularForm.AtkinLehnerDatum.q_pos A).ne'
  rw [ModularForm.alSlash_alSlash A k hF, ModularForm.heckeU_smul, smul_smul, ← zpow_add₀ hq0,
    show (2 - k) + (k - 2) = 0 by ring, zpow_zero, one_smul] at hTrW
  exact eq_neg_of_add_eq_zero_left hTrW
