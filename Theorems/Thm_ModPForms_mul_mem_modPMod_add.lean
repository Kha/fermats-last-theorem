import Definitions.Def_CuspForm_ModPForms
import P2M.Util
import P2M.Sol.S_ModPForms_mul_mem_modPMod_add
set_option autoImplicit false

theorem ModPForms.mul_mem_modPMod_add (N : ℕ) (a b : ℤ) (F : Type) [Field F]
    (φ ψ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N a F) (hψ : ψ ∈ ModPForms.modPMod N b F) :
    φ * ψ ∈ ModPForms.modPMod N (a + b) F := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_mul_mem_modPMod_add.solution
