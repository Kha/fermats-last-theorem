module

public import Definitions.Def_ModularCurve_LegendreJ
import P2M.Sol.S_ModularCurve_legendreJ_one_sub
import P2M.Sol.S_ModularCurve_legendreJ_inv
import P2M.Util
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Data.Finset.Insert
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace P2MW.S_ModularCurve_legendreJ_eq_legendreJ_iff

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "legendreJ legendreJ_one_sub legendreJ_inv"
p2m_open "ModularCurve"

theorem legendreJ_eq_legendreJ_iff' {K : Type*} [Field K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    {s t : K} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ s = legendreJ t ↔
      s ∈ ({t, 1 - t, t⁻¹, 1 - t⁻¹, (1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have hds : s ^ 2 * (s - 1) ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hs0) (pow_ne_zero _ (sub_ne_zero.mpr hs1))
    have hdt : t ^ 2 * (t - 1) ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ (sub_ne_zero.mpr ht1))
    simp only [legendreJ] at h
    rw [div_eq_div_iff hds hdt] at h
    have key : (2 : K) ^ 8 * ((s - t) * (s * t - 1) * (s + t - 1) * (s * t - s + 1)
        * (s * t - s - t) * (s * t - t + 1)) = 0 := by
      linear_combination h
    have key' := (mul_eq_zero.mp key).resolve_left (pow_ne_zero 8 h2)
    have hcases : s - t = 0 ∨ s * t - 1 = 0 ∨ s + t - 1 = 0 ∨ s * t - s + 1 = 0 ∨
        s * t - s - t = 0 ∨ s * t - t + 1 = 0 := by
      simpa only [mul_eq_zero, or_assoc] using key'
    rcases hcases with h | h | h | h | h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr <| Or.inr <| Or.inl (eq_inv_of_mul_eq_one_left (by linear_combination h))
    · exact Or.inr <| Or.inl (by linear_combination h)
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ?_
      exact eq_inv_of_mul_eq_one_left (by linear_combination -h)
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ?_
      have e : 1 - s = (1 - t)⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination h)
      rw [← e]; ring
    · refine Or.inr <| Or.inr <| Or.inr <| Or.inl ?_
      have e : 1 - s = t⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination -h)
      rw [← e]; ring
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [legendreJ_one_sub, legendreJ_inv]

end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_legendreJ_eq_legendreJ_iff.ModularCurve"

theorem solution {K : Type*} [Field K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    {s t : K} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ s = legendreJ t ↔
      s ∈ ({t, 1 - t, t⁻¹, 1 - t⁻¹, (1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K) :=
  ModularCurve.legendreJ_eq_legendreJ_iff' h2 hs0 hs1 ht0 ht1
end S_ModularCurve_legendreJ_eq_legendreJ_iff
end P2MW

public section
open ModularCurve
theorem ModularCurve.legendreJ_eq_legendreJ_iff {K : Type*} [Field K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    {s t : K} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ s = legendreJ t ↔
      s ∈ ({t, 1 - t, t⁻¹, 1 - t⁻¹, (1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_legendreJ_eq_legendreJ_iff.solution
end
