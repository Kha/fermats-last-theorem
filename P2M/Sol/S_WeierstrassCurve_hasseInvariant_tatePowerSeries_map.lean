module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import Definitions.Def_ModularCurve_TateFormal
public import Definitions.Def_ModularCurve_TateOrigin
import P2M.Sol.S_WeierstrassCurve_coeff_invariantDifferential_eq_hasseInvariant
import P2M.Sol.S_ModularCurve_one_add_single_mul_derivative_tateOriginX
import P2M.Sol.S_ModularCurve_tateOrigin_equation
import P2M.Util

namespace P2MW.S_WeierstrassCurve_hasseInvariant_tatePowerSeries_map

set_option autoImplicit false

open HahnSeries ModularCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "a₃ a₁ map mk a₄ a₂ a₆ hasseInvariant coeff_invariantDifferential_eq_hasseInvariant"
namespace HTasm
p2m_open "WeierstrassCurve"

theorem main (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    WeierstrassCurve.hasseInvariant q (ModularCurve.tatePowerSeries.map (PowerSeries.map (Int.castRingHom (ZMod q)))) = 1 := by
  have hp : q.Prime := Fact.out
  haveI : CharP (PowerSeries (ZMod q)) q := by
    refine charP_of_injective_ringHom (f := PowerSeries.C (R := ZMod q)) ?_ q
    intro a b h
    have := congrArg PowerSeries.constantCoeff h
    simpa using this
  set W : WeierstrassCurve (PowerSeries (ZMod q)) := ModularCurve.tatePowerSeries.map (PowerSeries.map (Int.castRingHom (ZMod q))) with hW
  have ha₁ : W.a₁ = 1 := by simp [hW, WeierstrassCurve.map]
  have ha₂ : W.a₂ = 0 := by simp [hW, WeierstrassCurve.map]
  have ha₃ : W.a₃ = 0 := by simp [hW, WeierstrassCurve.map]
  have ha₄ : W.a₄ = PowerSeries.map (Int.castRingHom (ZMod q)) tateA4 := by simp [hW, WeierstrassCurve.map]
  have ha₆ : W.a₆ = PowerSeries.map (Int.castRingHom (ZMod q)) tateA6 := by simp [hW, WeierstrassCurve.map]
  set x := tateOriginX (ZMod q) with hx
  set y := tateOriginY (ZMod q) with hy

  set p : PowerSeries (PowerSeries (ZMod q)) := PowerSeries.mk fun k => (-1 : PowerSeries (ZMod q)) ^ k with hpdef
  set ω : LaurentSeries (PowerSeries (ZMod q)) := HahnSeries.ofPowerSeries ℤ (PowerSeries (ZMod q)) p with hω
  have hp1 : (1 + PowerSeries.X) * p = 1 := by
    ext n
    rw [add_mul, one_mul, map_add, PowerSeries.coeff_one]
    cases n with
    | zero => simp [hpdef]
    | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, hpdef, PowerSeries.coeff_mk, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n), pow_succ]
      ring
  have hωT : ω * (1 + HahnSeries.single (1 : ℤ) (1 : PowerSeries (ZMod q))) = 1 := by
    rw [hω, ← HahnSeries.ofPowerSeries_X, ← RingHom.map_one (HahnSeries.ofPowerSeries ℤ (PowerSeries (ZMod q))), ← map_add, ← map_mul, mul_comm, hp1]

  have heq : y ^ 2 + HahnSeries.C W.a₁ * x * y + HahnSeries.C W.a₃ * y
      = x ^ 3 + HahnSeries.C W.a₂ * x ^ 2 + HahnSeries.C W.a₄ * x + HahnSeries.C W.a₆ := by
    rw [ha₁, ha₂, ha₃, ha₄, ha₆, map_one, map_zero]
    have h := tateOrigin_equation (ZMod q)
    rw [← hx, ← hy] at h
    linear_combination h
  have hωeq : ω * (2 * y + HahnSeries.C W.a₁ * x + HahnSeries.C W.a₃) = LaurentSeries.derivative (PowerSeries (ZMod q)) x := by
    rw [ha₁, ha₃, map_one, map_zero, one_mul, add_zero, ← one_add_single_mul_derivative_tateOriginX (ZMod q), ← hx,
      ← mul_assoc, hωT, one_mul]
  have hK := coeff_invariantDifferential_eq_hasseInvariant q hq W x y ω heq
    (coeff_tateOriginX_neg_two (ZMod q)) (fun n hn => coeff_tateOriginX_of_lt (ZMod q) hn)
    (coeff_tateOriginY_neg_three (ZMod q)) (fun n hn => coeff_tateOriginY_of_lt (ZMod q) hn) hωeq
  have hq1 : 1 ≤ q := hp.one_lt.le
  rw [← hK, hω, show ((q : ℤ) - 1) = ((q - 1 : ℕ) : ℤ) by omega, HahnSeries.ofPowerSeries_apply_coeff, hpdef,
    PowerSeries.coeff_mk, (hp.even_sub_one hq).neg_one_pow]

end WeierstrassCurve.HTasm

theorem solution (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    WeierstrassCurve.hasseInvariant q (ModularCurve.tatePowerSeries.map (PowerSeries.map (Int.castRingHom (ZMod q)))) = 1 :=
  WeierstrassCurve.HTasm.main q hq
end S_WeierstrassCurve_hasseInvariant_tatePowerSeries_map
end P2MW

public section
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.hasseInvariant_tatePowerSeries_map
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    WeierstrassCurve.hasseInvariant q (ModularCurve.tatePowerSeries.map (PowerSeries.map (Int.castRingHom (ZMod q)))) = 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_hasseInvariant_tatePowerSeries_map.solution
end
