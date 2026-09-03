import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0
import Theorems.Thm_ModularForm_mdifferentiable_heckeT
import Theorems.Thm_CuspFormClass_isZeroAt_heckeT
import P2M.Util
namespace P2MW.S_CuspForm_exists_coe_eq_heckeT

theorem solution {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) : ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = ModularForm.heckeT k p ⇑f := by
  haveI : NeZero N := ⟨fun h => hpN (h ▸ dvd_zero p)⟩
  exact ⟨{ toFun := ModularForm.heckeT k p ⇑f
           slash_action_eq' := fun γ hγ => ModularForm.heckeT_slash_eq_self_of_mem_Gamma0 k hp hpN
             (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) γ hγ
           holo' := ModularForm.mdifferentiable_heckeT (CuspFormClass.holo f) k p
           zero_at_cusps' := fun hc => CuspFormClass.isZeroAt_heckeT f p hc }, rfl⟩
