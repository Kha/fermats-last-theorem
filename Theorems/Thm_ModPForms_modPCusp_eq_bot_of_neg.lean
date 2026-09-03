import Definitions.Def_CuspForm_ModPForms
import P2M.Util
import P2M.Sol.S_ModPForms_modPCusp_eq_bot_of_neg
set_option autoImplicit false

theorem ModPForms.modPCusp_eq_bot_of_neg (N : ℕ) [NeZero N] (k : ℤ) (hk : k < 0) (F : Type) [Field F] :
    ModPForms.modPCusp N k F = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_modPCusp_eq_bot_of_neg.solution
