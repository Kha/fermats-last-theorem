module

import P2M.Sol.S_LaurentSeries_derivative_mul
import P2M.Util
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.RingTheory.LaurentSeries
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace P2MW.S_LaurentSeries_coeff_neg_one_inv_mul_derivative

set_option autoImplicit false

open HahnSeries

namespace LaurentSeries
p2m_export "LaurentSeries" "derivative hasseDeriv_coeff derivative_apply derivative_mul"
namespace R3
p2m_open "LaurentSeries"

variable {R : Type*} [CommRing R]

theorem coeff_derivative (x : LaurentSeries R) (n : ℤ) :
    (LaurentSeries.derivative R x).coeff n = ((n + 1 : ℤ) : R) * x.coeff (n + 1) := by
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right, zsmul_eq_mul]
  push_cast
  ring_nf

theorem derivative_single_one (k : ℤ) :
    LaurentSeries.derivative R (single k (1 : R)) = HahnSeries.C ((k : ℤ) : R) * single (k - 1) (1 : R) := by
  rw [HahnSeries.C_mul_eq_smul]
  ext n
  rw [coeff_derivative, HahnSeries.coeff_smul, HahnSeries.coeff_single, HahnSeries.coeff_single, smul_eq_mul]
  by_cases h : n + 1 = k
  · rw [if_pos h, if_pos (by omega), ← h, mul_one]
  · rw [if_neg h, if_neg (by omega), mul_zero, mul_zero]

theorem coeff_single_mul (b : ℤ) (x : LaurentSeries R) (n : ℤ) :
    (single b (1 : R) * x).coeff n = x.coeff (n - b) := by
  have h := HahnSeries.coeff_single_mul_add (r := (1 : R)) (x := x) (a := n - b) (b := b)
  rw [sub_add_cancel, one_mul] at h
  exact h

theorem single_mul_single_one (a b : ℤ) : single a (1 : R) * single b (1 : R) = single (a + b) 1 := by
  rw [HahnSeries.single_mul_single, mul_one]

theorem coeff_eq_zero_of_neg_of_mul_eq_one {w u : LaurentSeries R} (hu0 : u.coeff 0 = 1) (hu : ∀ n < 0, u.coeff n = 0)
    (h : w * u = 1) {n : ℤ} (hn : n < 0) : w.coeff n = 0 := by
  nontriviality R
  have hu_ne : u ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero (g := 0) (by rw [hu0]; exact one_ne_zero)
  have huord : u.order = 0 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [hu0]; exact one_ne_zero)) ?_
    by_contra hlt
    rw [not_le] at hlt
    exact hu_ne (HahnSeries.coeff_order_eq_zero.mp (hu _ hlt))
  have hulc : u.leadingCoeff = 1 := by rw [HahnSeries.leadingCoeff_eq, huord, hu0]
  have hw_ne : w ≠ 0 := by rintro rfl; rw [zero_mul] at h; exact zero_ne_one h
  have hword : 0 ≤ w.order := by
    by_contra hlt
    rw [not_le] at hlt
    have hc := HahnSeries.coeff_mul_order_add_order w u
    rw [h, huord, add_zero, hulc, mul_one, HahnSeries.coeff_one, if_neg hlt.ne] at hc
    exact (HahnSeries.leadingCoeff_ne_zero.mpr hw_ne) hc.symm
  exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hn hword)

theorem main (f g : LaurentSeries R) (k : ℤ) (hk : f.coeff k = 1) (hlt : ∀ n < k, f.coeff n = 0)
    (hinv : f * g = 1) :
    (g * LaurentSeries.derivative R f).coeff (-1) = (k : R) := by
  set u : LaurentSeries R := single (-k) (1 : R) * f with hu
  set w : LaurentSeries R := single k (1 : R) * g with hw
  have hucoeff : ∀ n, u.coeff n = f.coeff (n + k) := fun n => by
    rw [hu, coeff_single_mul]; ring_nf
  have hu0 : u.coeff 0 = 1 := by rw [hucoeff, zero_add, hk]
  have huneg : ∀ n < 0, u.coeff n = 0 := fun n hn => by rw [hucoeff]; exact hlt _ (by omega)
  have hf : f = single k (1 : R) * u := by
    rw [hu, ← mul_assoc, single_mul_single_one, add_neg_cancel]
    exact (one_mul f).symm
  have hwu : w * u = 1 := by
    rw [hw, hu]
    calc single k (1 : R) * g * (single (-k) 1 * f) = (single k (1 : R) * single (-k) 1) * (f * g) := by ring
      _ = 1 := by rw [single_mul_single_one, add_neg_cancel, hinv, mul_one]; rfl
  have hwneg : ∀ n < 0, w.coeff n = 0 := fun n hn => coeff_eq_zero_of_neg_of_mul_eq_one hu0 huneg hwu hn
  have hDuneg : ∀ n < 0, (LaurentSeries.derivative R u).coeff n = 0 := by
    intro n hn
    rw [coeff_derivative]
    rcases lt_or_eq_of_le (show n + 1 ≤ 0 by omega) with h | h
    · rw [huneg _ h, mul_zero]
    · rw [h, Int.cast_zero, zero_mul]

  rw [hf, LaurentSeries.derivative_mul, derivative_single_one, mul_add, HahnSeries.coeff_add]
  have hA : g * (HahnSeries.C ((k : ℤ) : R) * single (k - 1) (1 : R) * u) = HahnSeries.C ((k : ℤ) : R) * single (-1 : ℤ) (1 : R) := by
    have hs : single (k - 1) (1 : R) = single (-1 : ℤ) (1 : R) * single k 1 := by
      rw [single_mul_single_one, show (-1 : ℤ) + k = k - 1 by ring]
    calc g * (HahnSeries.C ((k : ℤ) : R) * single (k - 1) (1 : R) * u)
        = HahnSeries.C ((k : ℤ) : R) * (single (-1 : ℤ) (1 : R) * ((single k (1 : R) * g) * u)) := by rw [hs]; ring
      _ = HahnSeries.C ((k : ℤ) : R) * single (-1 : ℤ) (1 : R) := by rw [← hw, hwu, mul_one]
  have hB : (g * (single k (1 : R) * LaurentSeries.derivative R u)).coeff (-1) = 0 := by
    rw [← mul_assoc, mul_comm g, ← hw, HahnSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    exfalso
    by_cases hi : ij.1 < 0
    · exact (HahnSeries.mem_support _ _).mp h1 (hwneg _ hi)
    · exact (HahnSeries.mem_support _ _).mp h2 (hDuneg _ (by omega))
  rw [hA, hB, add_zero, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.coeff_single_same, smul_eq_mul, mul_one]

end LaurentSeries.R3

theorem solution {R : Type*} [CommRing R]
    (f g : LaurentSeries R) (k : ℤ) (hk : f.coeff k = 1) (hlt : ∀ n < k, f.coeff n = 0)
    (hinv : f * g = 1) :
    (g * LaurentSeries.derivative R f).coeff (-1) = (k : R) :=
  LaurentSeries.R3.main f g k hk hlt hinv
end S_LaurentSeries_coeff_neg_one_inv_mul_derivative
end P2MW

public section
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

theorem LaurentSeries.coeff_neg_one_inv_mul_derivative {R : Type*} [CommRing R]
    (f g : LaurentSeries R) (k : ℤ) (hk : f.coeff k = 1) (hlt : ∀ n < k, f.coeff n = 0)
    (hinv : f * g = 1) :
    (g * LaurentSeries.derivative R f).coeff (-1) = (k : R) := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_coeff_neg_one_inv_mul_derivative.solution
end
