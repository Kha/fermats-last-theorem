import Definitions.Def_CuspForm_ModPForms
import P2M.Util
import P2M.Sol.S_ModPForms_modPCusp_le_modPMod
set_option autoImplicit false

theorem ModPForms.modPCusp_le_modPMod (N' : ℕ) [NeZero N'] (k : ℤ) (F : Type) [Field F] :
    modPCusp N' k F ≤ modPMod N' k F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_modPCusp_le_modPMod.solution
