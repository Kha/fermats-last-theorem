module

public import Mathlib
public import Definitions.Def_ModularCurve_TateFormal
public import Definitions.Def_ModularCurve_X0
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_c4_tateLaurent

set_option autoImplicit false

p2m_open "PowerSeries HahnSeries ModularCurve P2MW.S_ModularCurve_c4_tateLaurent.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "tateA4 coeff_tateA4 tatePowerSeries tatePowerSeries_a₁ tatePowerSeries_a₂ tatePowerSeries_a₃ tatePowerSeries_a₄ laurentOfInt_apply tateLaurent eisenstein4"
namespace TD1
p2m_open "ModularCurve"

theorem c₄_tatePowerSeries : tatePowerSeries.c₄ = 1 - 48 * tateA4 := by
  rw [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, tatePowerSeries_a₁, tatePowerSeries_a₂,
    tatePowerSeries_a₃, tatePowerSeries_a₄]
  ring

theorem one_sub_48_tateA4 : (1 - 48 * tateA4 : PowerSeries ℤ) = eisenstein4 := by
  ext n
  have h48 : (48 : PowerSeries ℤ) * tateA4 = (48 : ℕ) • tateA4 := by
    rw [nsmul_eq_mul, Nat.cast_ofNat]
  rw [map_sub, PowerSeries.coeff_one, eisenstein4, PowerSeries.coeff_mk, h48, map_nsmul, coeff_tateA4,
    nsmul_eq_mul, Nat.cast_ofNat]
  split_ifs with h
  · subst h; simp
  · simp only [zero_sub, mul_neg, neg_neg, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring

theorem main (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) eisenstein4) := by
  rw [tateLaurent, WeierstrassCurve.map_c₄, c₄_tatePowerSeries, one_sub_48_tateA4, laurentOfInt_apply]

end ModularCurve.TD1

open PowerSeries HahnSeries in
theorem solution (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) eisenstein4) :=
  ModularCurve.TD1.main K
