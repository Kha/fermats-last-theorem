import Mathlib
import Definitions.Def_CuspForm_ModPForms
import P2M.Util
import P2M.Sol.S_ModPForms_one_mem_modPMod_zero
set_option autoImplicit false

theorem ModPForms.one_mem_modPMod_zero (N : ℕ) (F : Type) [Field F] :
    (1 : PowerSeries F) ∈ ModPForms.modPMod N 0 F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_one_mem_modPMod_zero.solution
