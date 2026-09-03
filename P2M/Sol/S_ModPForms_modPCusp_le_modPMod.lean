import Definitions.Def_CuspForm_ModPForms
import P2M.Util
namespace P2MW.S_ModPForms_modPCusp_le_modPMod
set_option autoImplicit false

open ModPForms

theorem solution (N' : ℕ) [NeZero N'] (k : ℤ) (F : Type) [Field F] :
    modPCusp N' k F ≤ modPMod N' k F := by
  refine Submodule.span_mono ?_
  rintro φ ⟨f, a, ha, hφ⟩
  exact ⟨(f : ModularForm (CongruenceSubgroup.Gamma0 N') k), a, ha, hφ⟩
