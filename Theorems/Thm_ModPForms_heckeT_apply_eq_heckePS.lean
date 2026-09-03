import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import P2M.Util
import P2M.Sol.S_ModPForms_heckeT_apply_eq_heckePS
set_option autoImplicit false

theorem ModPForms.heckeT_apply_eq_heckePS (F : Type) [Field F] (k : ℕ) (hk : 1 ≤ k) (ℓ : ℕ) (φ : PowerSeries F) :
    PowerSeries.heckeT ℓ k φ = ModPForms.heckePS (k : ℤ) ℓ φ := by p2m_exact_reverting @_root_.P2MW.S_ModPForms_heckeT_apply_eq_heckePS.solution
