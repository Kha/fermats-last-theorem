module

public import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Sol.S_AlgebraicCurve_Place_evalAt_zpow
import P2M.Util
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

namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_zpow_left

open AlgebraicCurve AlgebraicCurve.Divisor

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {f : F} (hf : f ≠ 0) {D : Divisor K F} (n : ℤ) (hrat : ∀ v ∈ D.support, Place.IsRational v) (hord : ∀ v ∈ D.support, Place.ord v f = 0) : Divisor.evalFun (f ^ n) D = Divisor.evalFun f D ^ n := by
  rw [evalFun_def, evalFun_def, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [AlgebraicCurve.Place.evalAt_zpow v (hrat v hv) hf (hord v hv) n, ← zpow_mul, ← zpow_mul, mul_comm]
end S_AlgebraicCurve_Divisor_evalFun_zpow_left
end P2MW

public section
open AlgebraicCurve
theorem AlgebraicCurve.Divisor.evalFun_zpow_left {K F : Type*} [Field K] [Field F] [Algebra K F] {f : F} (hf : f ≠ 0) {D : Divisor K F} (n : ℤ) (hrat : ∀ v ∈ D.support, Place.IsRational v) (hord : ∀ v ∈ D.support, Place.ord v f = 0) : Divisor.evalFun (f ^ n) D = Divisor.evalFun f D ^ n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_evalFun_zpow_left.solution
end
