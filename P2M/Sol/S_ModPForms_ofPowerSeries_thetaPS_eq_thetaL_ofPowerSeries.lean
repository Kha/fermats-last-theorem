import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_QExpansionDiff
import P2M.Util
namespace P2MW.S_ModPForms_ofPowerSeries_thetaPS_eq_thetaL_ofPowerSeries

set_option autoImplicit false

theorem solution
    (K : Type) [Field K] (φ : PowerSeries K) :
    HahnSeries.ofPowerSeries ℤ K (ModPForms.thetaPS φ) =
      ModularCurve.thetaL K (HahnSeries.ofPowerSeries ℤ K φ) := by
  ext n
  rw [ModularCurve.thetaL_apply, LaurentSeries.derivative_apply, ← sub_add_cancel n 1,
    HahnSeries.coeff_single_mul_add, LaurentSeries.hasseDeriv_coeff, Nat.cast_one, sub_add_cancel, one_mul,
    Ring.choose_one_right]
  change ((ModPForms.thetaPS φ : PowerSeries K) : LaurentSeries K).coeff n =
    n • ((φ : PowerSeries K) : LaurentSeries K).coeff n
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hn
  · rw [smul_zero]
  · rw [ModPForms.thetaPS, PowerSeries.coeff_mk, zsmul_eq_mul]
    congr 1
    have h1 : ((n.natAbs : ℤ) : K) = ((n : ℤ) : K) := by rw [Int.natAbs_of_nonneg (not_lt.mp hn)]
    rw [Int.cast_natCast] at h1
    exact h1
