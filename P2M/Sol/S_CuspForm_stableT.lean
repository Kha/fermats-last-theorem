import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_ModularForm_heckeU_add_slash_slash_eq_self_of_mem_GammaH
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0
import P2M.Util
namespace P2MW.S_CuspForm_stableT

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    CuspForm.StableT M H k ℓ := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  intro ρ hρ f
  refine ⟨fun γ hγ => ModularForm.heckeU_add_slash_slash_eq_self_of_mem_GammaH M H k hℓ hℓM ρ hρ
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ,
    (ModularForm.mdifferentiable_heckeU (CuspFormClass.holo f) k ℓ).add ((CuspFormClass.holo f).slash k _),
    fun c hc => ?_⟩
  rw [SlashAction.slash_mul]
  exact (CuspFormClass.isZeroAt_heckeU f ℓ hc).add
    (CuspFormClass.isZeroAt_slash_slash_heckeDiagMatrix_of_mem_Gamma0 M H k ℓ ρ f hc)
