import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import P2M.Util
namespace P2MW.S_ModularCurve_unitsMap_div_eq_one_imp_mem_unitsMap_ker_mul

set_option autoImplicit false

open scoped MatrixGroups

namespace ModularCurve
p2m_open "ModularCurve"

theorem unitsMap_eq_one_iff_of_eq {M a b : ℕ} (hab : a = b) (ha : a ∣ M) (hb : b ∣ M) (u : (ZMod M)ˣ) :
    ZMod.unitsMap ha u = 1 ↔ ZMod.unitsMap hb u = 1 := by
  subst hab
  rfl

end ModularCurve

theorem solution (q M₀ : ℕ) [Fact q.Prime] [NeZero M₀]
    (hpM : q ∣ M₀ * q) (u : (ZMod (M₀ * q))ˣ) (hu : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1) :
    u ∈ (ZMod.unitsMap (dvd_mul_right M₀ q)).ker := by
  rw [MonoidHom.mem_ker]
  exact (ModularCurve.unitsMap_eq_one_iff_of_eq (Nat.mul_div_cancel M₀ (Fact.out : q.Prime).pos) _ _ u).mp hu
