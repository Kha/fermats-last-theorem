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

namespace P2MW.S_ModularCurve_legendreJ_inv

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "legendreJ"
p2m_open "ModularCurve"

theorem legendreJ_inv' {K : Type*} [Field K] (t : K) : legendreJ t⁻¹ = legendreJ t := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [inv_zero]
  have hi : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
  have hu : (t⁻¹ : K) ≠ 0 := inv_ne_zero ht
  have e1 : (t⁻¹ ^ 2 - t⁻¹ + 1) ^ 3 = (t ^ 2 - t + 1) ^ 3 * t⁻¹ ^ 6 := by
    linear_combination (-t^5*t⁻¹^5 + 3*t^4*t⁻¹^5 - t^4*t⁻¹^4 - 6*t^3*t⁻¹^5 + 3*t^3*t⁻¹^4 - t^3*t⁻¹^3 + 7*t^2*t⁻¹^5 - 6*t^2*t⁻¹^4 + 3*t^2*t⁻¹^3 - t^2*t⁻¹^2 - 6*t*t⁻¹^5 + 7*t*t⁻¹^4 - 6*t*t⁻¹^3 + 3*t*t⁻¹^2 - t*t⁻¹ + 3*t⁻¹^5 - 6*t⁻¹^4 + 7*t⁻¹^3 - 6*t⁻¹^2 + 3*t⁻¹ - 1) * hi
  have e2 : t⁻¹ ^ 2 * (t⁻¹ - 1) ^ 2 = (t ^ 2 * (t - 1) ^ 2) * t⁻¹ ^ 6 := by
    linear_combination (-t^3*t⁻¹^5 + 2*t^2*t⁻¹^5 - t^2*t⁻¹^4 - t*t⁻¹^5 + 2*t*t⁻¹^4 - t*t⁻¹^3 - t⁻¹^4 + 2*t⁻¹^3 - t⁻¹^2) * hi
  simp only [legendreJ]
  rw [e1, e2, ← mul_assoc, mul_div_mul_right _ _ (pow_ne_zero 6 hu)]

end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_legendreJ_inv.ModularCurve"

theorem solution {K : Type*} [Field K] (t : K) : legendreJ t⁻¹ = legendreJ t :=
  ModularCurve.legendreJ_inv' t
end S_ModularCurve_legendreJ_inv
end P2MW

public section
open ModularCurve
theorem ModularCurve.legendreJ_inv {K : Type*} [Field K] (t : K) : legendreJ t⁻¹ = legendreJ t := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_legendreJ_inv.solution
end
