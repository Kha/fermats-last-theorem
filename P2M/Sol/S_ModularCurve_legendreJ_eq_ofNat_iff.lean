module

public import Definitions.Def_ModularCurve_LegendreJ
import P2M.Util
public import Mathlib.Algebra.GroupWithZero.Units.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace P2MW.S_ModularCurve_legendreJ_eq_ofNat_iff

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "legendreJ"
p2m_open "ModularCurve"

theorem legendreJ_eq_ofNat_iff' {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 1728 ↔ t = -1 ∨ t = 2 ∨ t = 2⁻¹ := by
  have hden : t ^ 2 * (t - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ (sub_ne_zero.mpr ht1))
  have h64 : (64 : K) ≠ 0 := by
    rw [show (64 : K) = 2 ^ 6 by norm_num]; exact pow_ne_zero _ h2
  rw [legendreJ, div_eq_iff hden]
  constructor
  · intro h
    have key : (64 : K) * ((t + 1) ^ 2 * ((t - 2) ^ 2 * (2 * t - 1) ^ 2)) = 0 := by
      linear_combination h
    have key' := (mul_eq_zero.mp key).resolve_left h64
    rcases mul_eq_zero.mp key' with h | h
    · exact Or.inl (add_eq_zero_iff_eq_neg.mp ((pow_eq_zero_iff two_ne_zero).mp h))
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h)))
    · have h' : 2 * t - 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h
      exact Or.inr (Or.inr (eq_inv_of_mul_eq_one_right (by linear_combination h')))
  · rintro (rfl | rfl | ht)
    · norm_num
    · norm_num
    · have h2t : (2 : K) * t = 1 := by rw [ht, mul_inv_cancel₀ h2]
      linear_combination
        (128 * t ^ 5 - 320 * t ^ 4 - 256 * t ^ 3 + 704 * t ^ 2 + 256 * t - 256) * h2t

end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_legendreJ_eq_ofNat_iff.ModularCurve"

theorem solution {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 1728 ↔ t = -1 ∨ t = 2 ∨ t = 2⁻¹ :=
  ModularCurve.legendreJ_eq_ofNat_iff' h2 ht0 ht1
end S_ModularCurve_legendreJ_eq_ofNat_iff
end P2MW

public section
open ModularCurve
theorem ModularCurve.legendreJ_eq_ofNat_iff {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 1728 ↔ t = -1 ∨ t = 2 ∨ t = 2⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_legendreJ_eq_ofNat_iff.solution
end
