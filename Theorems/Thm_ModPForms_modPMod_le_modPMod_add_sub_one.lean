import Definitions.Def_CuspForm_ModPForms
import P2M.Util
import P2M.Sol.S_ModPForms_modPMod_le_modPMod_add_sub_one
set_option autoImplicit false

theorem ModPForms.modPMod_le_modPMod_add_sub_one (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] (k : ℤ)
    (F : Type) [Field F] [CharP F p] :
    modPMod N' k F ≤ modPMod N' (k + ((p : ℤ) - 1)) F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_modPMod_le_modPMod_add_sub_one.solution
