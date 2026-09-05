module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.RingTheory.LaurentSeries
import Definitions.Def_ModularCurve_X0
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def tateOriginX (K : Type*) [CommRing K] : LaurentSeries (PowerSeries K) :=
  HahnSeries.single (-2 : ℤ) (1 : PowerSeries K) + HahnSeries.single (-1 : ℤ) (1 : PowerSeries K) +
    HahnSeries.ofPowerSeries ℤ (PowerSeries K) (PowerSeries.mk fun k => PowerSeries.mk fun M =>
      if M = 0 then 0 else
        (∑ e ∈ M.divisors, (e : K) * ((e.choose k : K) + (-1) ^ k * ((e + k - 1).choose k : K)))
          - (if k = 0 then 2 * ∑ e ∈ M.divisors, (e : K) else 0))

def tateOriginY (K : Type*) [CommRing K] : LaurentSeries (PowerSeries K) :=
  HahnSeries.single (-3 : ℤ) (-1 : PowerSeries K) + HahnSeries.single (-2 : ℤ) (-2 : PowerSeries K) +
    HahnSeries.single (-1 : ℤ) (-1 : PowerSeries K) +
    HahnSeries.ofPowerSeries ℤ (PowerSeries K) (PowerSeries.mk fun k => PowerSeries.mk fun M =>
      if M = 0 then 0 else
        (∑ e ∈ M.divisors, ((e.choose 2 : K) * (e.choose k : K)
            - ((e + 1).choose 2 : K) * ((-1) ^ k * ((e + k - 1).choose k : K))))
          + (if k = 0 then ∑ e ∈ M.divisors, (e : K) else 0))

theorem coeff_tateOriginX_neg_two (K : Type*) [CommRing K] : (tateOriginX K).coeff (-2) = 1 := by
  rw [tateOriginX, HahnSeries.coeff_add, HahnSeries.coeff_add, ofPowerSeries_coeff_of_neg _ (by norm_num),
    HahnSeries.coeff_single, HahnSeries.coeff_single, if_pos rfl, if_neg (by norm_num), add_zero, add_zero]

theorem coeff_tateOriginX_of_lt (K : Type*) [CommRing K] {n : ℤ} (hn : n < -2) :
    (tateOriginX K).coeff n = 0 := by
  have h1 : n ≠ -2 := by omega
  have h2 : n ≠ -1 := by omega
  rw [tateOriginX, HahnSeries.coeff_add, HahnSeries.coeff_add, ofPowerSeries_coeff_of_neg _ (by omega),
    HahnSeries.coeff_single, HahnSeries.coeff_single, if_neg h1, if_neg h2, add_zero, add_zero]

theorem coeff_tateOriginY_neg_three (K : Type*) [CommRing K] : (tateOriginY K).coeff (-3) = -1 := by
  rw [tateOriginY, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add,
    ofPowerSeries_coeff_of_neg _ (by norm_num), HahnSeries.coeff_single, HahnSeries.coeff_single,
    HahnSeries.coeff_single, if_pos rfl, if_neg (by norm_num), if_neg (by norm_num), add_zero, add_zero, add_zero]

theorem coeff_tateOriginY_of_lt (K : Type*) [CommRing K] {n : ℤ} (hn : n < -3) :
    (tateOriginY K).coeff n = 0 := by
  have h1 : n ≠ -3 := by omega
  have h2 : n ≠ -2 := by omega
  have h3 : n ≠ -1 := by omega
  rw [tateOriginY, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add,
    ofPowerSeries_coeff_of_neg _ (by omega), HahnSeries.coeff_single, HahnSeries.coeff_single,
    HahnSeries.coeff_single, if_neg h1, if_neg h2, if_neg h3, add_zero, add_zero, add_zero]

end ModularCurve

end
