import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import P2M.Util
namespace P2MW.S_ModPForms_heckeT_apply_eq_heckePS

set_option autoImplicit false

theorem solution (F : Type) [Field F] (k : ℕ) (hk : 1 ≤ k) (ℓ : ℕ) (φ : PowerSeries F) :
    PowerSeries.heckeT ℓ k φ = ModPForms.heckePS (k : ℤ) ℓ φ := by
  ext n
  unfold ModPForms.heckePS
  rw [PowerSeries.coeff_heckeT, PowerSeries.coeff_mk, mul_comm ℓ n, mul_ite, mul_zero,
    show ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]
