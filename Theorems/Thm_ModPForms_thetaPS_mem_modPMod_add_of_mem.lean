import Definitions.Def_CuspForm_ModPForms
import P2M.Util
import P2M.Sol.S_ModPForms_thetaPS_mem_modPMod_add_of_mem
set_option autoImplicit false

theorem ModPForms.thetaPS_mem_modPMod_add_of_mem (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] (k : ℤ)
    (F : Type) [Field F] [CharP F p] (φ : PowerSeries F) (hφ : φ ∈ modPMod N' k F) :
    thetaPS φ ∈ modPMod N' (k + ((p : ℤ) + 1)) F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_thetaPS_mem_modPMod_add_of_mem.solution
