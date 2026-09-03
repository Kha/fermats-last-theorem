import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_GammaH
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_heckeU
import P2M.Util
namespace P2MW.S_CuspForm_stableU

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ}
    (hq : q.Prime) (hqM : q ∣ M) :
    CuspForm.StableU M H k q := by
  intro f
  exact ⟨fun γ hγ => ModularForm.heckeU_slash_eq_self_of_mem_GammaH M H k hq hqM
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ,
    ModularForm.mdifferentiable_heckeU (CuspFormClass.holo f) k q,
    fun c hc => CuspFormClass.isZeroAt_heckeU f q hc⟩
