module

public import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Sol.S_AlgebraicCurve_Place_evalAt_mul
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

namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_mul

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {f g : F} {D : Divisor K F} (hrat : ∀ v ∈ D.support, Place.IsRational v) (hf : ∀ v ∈ D.support, f ∈ v.toValuationSubring) (hg : ∀ v ∈ D.support, g ∈ v.toValuationSubring) : Divisor.evalFun (f * g) D = Divisor.evalFun f D * Divisor.evalFun g D := by
  rw [show Divisor.evalFun (f * g) D = D.prod fun v n => v.evalAt f ^ n * v.evalAt g ^ n from
    Finsupp.prod_congr fun v hv => by
      rw [AlgebraicCurve.Place.evalAt_mul v (hrat v hv) (hf v hv) (hg v hv), mul_zpow]]
  exact Finsupp.prod_mul
end S_AlgebraicCurve_Divisor_evalFun_mul
end P2MW

public section
open AlgebraicCurve
theorem AlgebraicCurve.Divisor.evalFun_mul {K F : Type*} [Field K] [Field F] [Algebra K F] {f g : F} {D : Divisor K F} (hrat : ∀ v ∈ D.support, Place.IsRational v) (hf : ∀ v ∈ D.support, f ∈ v.toValuationSubring) (hg : ∀ v ∈ D.support, g ∈ v.toValuationSubring) : Divisor.evalFun (f * g) D = Divisor.evalFun f D * Divisor.evalFun g D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_evalFun_mul.solution
end
