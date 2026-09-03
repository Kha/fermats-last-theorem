import Mathlib
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Theorems.Thm_ModularForm_alSlash_heckeT_comm
import Theorems.Thm_CuspForm_heckeTLin_heckeULin_comm
import P2M.Util
namespace P2MW.S_CuspForm_traceLin_heckeTLin

set_option autoImplicit false

open ModularForm

theorem solution {M q : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓR : ¬ ℓ ∣ A.R) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    CuspForm.traceLin A hq (CuspForm.heckeTLin 2 hℓ hℓM f) = CuspForm.heckeTLin 2 hℓ hℓR (CuspForm.traceLin A hq f) := by
  have hqM : q ∣ M := ⟨A.R, A.hM⟩
  refine DFunLike.coe_injective ?_
  show ⇑(CuspForm.traceLin A hq (CuspForm.heckeTLin 2 hℓ hℓM f)) = ⇑(CuspForm.heckeTLin 2 hℓ hℓR (CuspForm.traceLin A hq f))
  rw [CuspForm.coe_traceLin_apply, CuspForm.coe_heckeTLin_apply, CuspForm.coe_heckeTLin_apply,
    CuspForm.coe_traceLin_apply, heckeT_add]
  congr 1

  have hw : alSlash A 2 (heckeT 2 ℓ ⇑f) = heckeT 2 ℓ (alSlash A 2 ⇑f) :=
    ModularForm.alSlash_heckeT_comm A 2 hℓ hℓM (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ)
  rw [hw]

  have hc := CuspForm.heckeTLin_heckeULin_comm (N := M) 2 hℓ hℓM hqM
  have h := congrArg (fun g : CuspForm (CongruenceSubgroup.Gamma0 M) 2 => (⇑g : UpperHalfPlane → ℂ))
    (LinearMap.ext_iff.mp hc.eq (CuspForm.atkinLehnerLin A 2 f))
  simpa only [Module.End.mul_apply, CuspForm.coe_heckeTLin_apply, CuspForm.coe_heckeULin_apply,
    CuspForm.coe_atkinLehnerLin_apply] using h.symm
