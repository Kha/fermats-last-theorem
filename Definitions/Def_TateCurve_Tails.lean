module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Ring.Ultra
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

open scoped NNReal
open IsUltrametricDist

namespace TateCurve

section Coefficients

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

private theorem norm_add_le_max' (a b : K) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
  exact_mod_cast nnnorm_add_le_max a b

private theorem norm_sub_le_max' (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  simpa [norm_neg] using norm_add_le_max' a (-b)

noncomputable def xDivTerm (u : K) (d : ℕ) : K := (d : K) * (u ^ d + u⁻¹ ^ d - 2)

noncomputable def yDivTerm (u : K) (d : ℕ) : K :=
  ((d.choose 2 : ℕ) : K) * (u ^ d - u⁻¹ ^ d) - (d : K) * u⁻¹ ^ d + (d : K)

noncomputable def xCoeff (u : K) (N : ℕ) : K := ∑ d ∈ N.divisors, xDivTerm u d

noncomputable def yCoeff (u : K) (N : ℕ) : K := ∑ d ∈ N.divisors, yDivTerm u d

noncomputable def growthBound (u : K) : ℝ := max (max ‖u‖ ‖u⁻¹‖) 1

theorem one_le_growthBound (u : K) : 1 ≤ growthBound u := le_max_right _ _

theorem growthBound_nonneg (u : K) : 0 ≤ growthBound u :=
  zero_le_one.trans (one_le_growthBound u)

theorem norm_pow_le_growthBound (u : K) (d : ℕ) : ‖u ^ d‖ ≤ growthBound u ^ d := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg u) ((le_max_left _ _).trans (le_max_left _ _)) d

theorem norm_inv_pow_le_growthBound (u : K) (d : ℕ) : ‖u⁻¹ ^ d‖ ≤ growthBound u ^ d := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((le_max_right _ _).trans (le_max_left _ _)) d

theorem one_le_growthBound_pow (u : K) (d : ℕ) : (1 : ℝ) ≤ growthBound u ^ d :=
  one_le_pow₀ (one_le_growthBound u)

theorem norm_natCast_le_growthBound_pow (u : K) (k d : ℕ) :
    ‖(k : K)‖ ≤ growthBound u ^ d :=
  (IsUltrametricDist.norm_natCast_le_one K k).trans (one_le_growthBound_pow u d)

theorem norm_xDivTerm_le (u : K) (d : ℕ) : ‖xDivTerm u d‖ ≤ growthBound u ^ d := by
  rw [xDivTerm]
  calc ‖(d : K) * (u ^ d + u⁻¹ ^ d - 2)‖
      = ‖(d : K)‖ * ‖u ^ d + u⁻¹ ^ d - 2‖ := norm_mul _ _
    _ ≤ 1 * ‖u ^ d + u⁻¹ ^ d - 2‖ :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one K d)
          (norm_nonneg _)
    _ = ‖u ^ d + (u⁻¹ ^ d - 2)‖ := by rw [one_mul, add_sub_assoc]
    _ ≤ max ‖u ^ d‖ ‖u⁻¹ ^ d - 2‖ := norm_add_le_max' _ _
    _ ≤ growthBound u ^ d := by
        refine max_le (norm_pow_le_growthBound u d) ?_
        refine (norm_sub_le_max' _ _).trans
          (max_le (norm_inv_pow_le_growthBound u d) ?_)
        calc ‖(2 : K)‖ = ‖((2 : ℕ) : K)‖ := by norm_num
          _ ≤ growthBound u ^ d := norm_natCast_le_growthBound_pow u 2 d

theorem norm_yDivTerm_le (u : K) (d : ℕ) : ‖yDivTerm u d‖ ≤ growthBound u ^ d := by
  rw [yDivTerm]
  refine (norm_add_le_max' _ _).trans (max_le ?_ ?_)
  · refine (norm_sub_le_max' _ _).trans (max_le ?_ ?_)
    · calc ‖((d.choose 2 : ℕ) : K) * (u ^ d - u⁻¹ ^ d)‖
          = ‖((d.choose 2 : ℕ) : K)‖ * ‖u ^ d - u⁻¹ ^ d‖ := norm_mul _ _
        _ ≤ 1 * ‖u ^ d - u⁻¹ ^ d‖ :=
            mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one K _)
              (norm_nonneg _)
        _ = ‖u ^ d - u⁻¹ ^ d‖ := one_mul _
        _ ≤ max ‖u ^ d‖ ‖u⁻¹ ^ d‖ := norm_sub_le_max' _ _
        _ ≤ growthBound u ^ d := max_le (norm_pow_le_growthBound u d)
            (norm_inv_pow_le_growthBound u d)
    · calc ‖(d : K) * u⁻¹ ^ d‖ = ‖(d : K)‖ * ‖u⁻¹ ^ d‖ := norm_mul _ _
        _ ≤ 1 * (growthBound u ^ d) :=
            mul_le_mul (IsUltrametricDist.norm_natCast_le_one K d)
              (norm_inv_pow_le_growthBound u d) (norm_nonneg _) zero_le_one
        _ = growthBound u ^ d := one_mul _
  · exact norm_natCast_le_growthBound_pow u d d

end Coefficients

end TateCurve
