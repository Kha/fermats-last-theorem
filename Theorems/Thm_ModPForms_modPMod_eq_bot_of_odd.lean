import Definitions.Def_CuspForm_ModPForms
import P2M.Util
import P2M.Sol.S_ModPForms_modPMod_eq_bot_of_odd
set_option autoImplicit false
theorem ModPForms.modPMod_eq_bot_of_odd (N : ℕ) (k : ℤ) (hk : Odd k) (F : Type) [Field F] :
    ModPForms.modPMod N k F = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_modPMod_eq_bot_of_odd.solution
