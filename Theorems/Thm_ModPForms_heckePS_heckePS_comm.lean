import Mathlib
import Definitions.Def_CuspForm_ModPForms
import P2M.Util
import P2M.Sol.S_ModPForms_heckePS_heckePS_comm
set_option autoImplicit false

theorem ModPForms.heckePS_heckePS_comm
    (F : Type) [Field F] (k : ℤ) (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (φ : PowerSeries F) :
    ModPForms.heckePS k ℓ (ModPForms.heckePS k ℓ' φ) = ModPForms.heckePS k ℓ' (ModPForms.heckePS k ℓ φ) := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_heckePS_heckePS_comm.solution
