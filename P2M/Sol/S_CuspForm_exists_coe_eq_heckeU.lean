import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0
import Theorems.Thm_ModularForm_mdifferentiable_heckeU
import Theorems.Thm_CuspFormClass_isZeroAt_heckeU
import P2M.Util
namespace P2MW.S_CuspForm_exists_coe_eq_heckeU

theorem solution {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ} (hpN : p ∣ N) : ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeU k p ⇑f :=
  ⟨{ toFun := ModularForm.heckeU k p ⇑f
     slash_action_eq' := fun γ hγ => ModularForm.heckeU_slash_eq_self_of_mem_Gamma0 k hpN
       (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
     holo' := ModularForm.mdifferentiable_heckeU (CuspFormClass.holo f) k p
     zero_at_cusps' := fun hc => CuspFormClass.isZeroAt_heckeU f p hc }, rfl⟩
