import Definitions.Def_CuspForm_ModPForms
import P2M.Util
import P2M.Sol.S_ModPForms_modPMod_le_modPMod_of_dvd
set_option autoImplicit false
theorem ModPForms.modPMod_le_modPMod_of_dvd (M N : ℕ) (hMN : M ∣ N) (k : ℤ) (F : Type) [Field F] :
    ModPForms.modPMod M k F ≤ ModPForms.modPMod N k F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_modPMod_le_modPMod_of_dvd.solution
