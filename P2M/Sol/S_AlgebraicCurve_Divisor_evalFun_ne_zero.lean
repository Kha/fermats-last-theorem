module

public import Definitions.Def_AlgebraicCurve_PlaceEvaluation
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_ne_zero

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {f : F} {D : Divisor K F} (h : ∀ v ∈ D.support, Place.evalAt v f ≠ 0) : Divisor.evalFun f D ≠ 0 := by
  rw [Divisor.evalFun_def]
  exact Finset.prod_ne_zero_iff.mpr fun v hv => zpow_ne_zero _ (h v hv)
end S_AlgebraicCurve_Divisor_evalFun_ne_zero
end P2MW

public section
open AlgebraicCurve
theorem AlgebraicCurve.Divisor.evalFun_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] {f : F} {D : Divisor K F} (h : ∀ v ∈ D.support, Place.evalAt v f ≠ 0) : Divisor.evalFun f D ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_evalFun_ne_zero.solution
end
