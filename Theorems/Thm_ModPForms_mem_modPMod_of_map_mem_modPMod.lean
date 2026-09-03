import Mathlib
import Definitions.Def_CuspForm_ModPForms
import P2M.Util
import P2M.Sol.S_ModPForms_mem_modPMod_of_map_mem_modPMod
set_option autoImplicit false

theorem ModPForms.mem_modPMod_of_map_mem_modPMod
    (N : ℕ) (k : ℤ) (K L : Type) [Field K] [Field L] (i : K →+* L)
    (ψ : PowerSeries K) (h : PowerSeries.map i ψ ∈ ModPForms.modPMod N k L) :
    ψ ∈ ModPForms.modPMod N k K := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_mem_modPMod_of_map_mem_modPMod.solution
