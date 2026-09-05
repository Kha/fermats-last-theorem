module

public import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Sol.S_AlgebraicCurve_Divisor_evalFun_add
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

namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_single_sub_single

open AlgebraicCurve AlgebraicCurve.Divisor

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F) {v₁ v₂ : Place K F} (h₁ : v₁.evalAt f ≠ 0) (h₂ : v₂.evalAt f ≠ 0) : Divisor.evalFun f (Finsupp.single v₁ 1 + Finsupp.single v₂ (-1)) = v₁.evalAt f / v₂.evalAt f := by
  have hsupp : ∀ (w : Place K F) (n : ℤ), w.evalAt f ≠ 0 →
      ∀ v ∈ (Finsupp.single w n).support, Place.evalAt v f ≠ 0 := by
    intro w n hw v hv
    have := Finsupp.support_single_subset hv
    rw [Finset.mem_singleton] at this
    rw [this]
    exact hw
  rw [AlgebraicCurve.Divisor.evalFun_add f (hsupp v₁ 1 h₁) (hsupp v₂ (-1) h₂), evalFun_single, evalFun_single,
    zpow_one, zpow_neg_one, div_eq_mul_inv]
end S_AlgebraicCurve_Divisor_evalFun_single_sub_single
end P2MW

public section
open AlgebraicCurve
theorem AlgebraicCurve.Divisor.evalFun_single_sub_single {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F) {v₁ v₂ : Place K F} (h₁ : v₁.evalAt f ≠ 0) (h₂ : v₂.evalAt f ≠ 0) : Divisor.evalFun f (Finsupp.single v₁ 1 + Finsupp.single v₂ (-1)) = v₁.evalAt f / v₂.evalAt f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_evalFun_single_sub_single.solution
end
