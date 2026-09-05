module

public import Definitions.Def_ModularCurve_TateFormal
public import Definitions.Def_ModularCurve_X0
import P2M.Util
public import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

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
end S_ModularCurve_c4_tateLaurent
end P2MW

public section
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve
open PowerSeries HahnSeries in

theorem ModularCurve.c4_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) eisenstein4) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_c4_tateLaurent.solution
end
