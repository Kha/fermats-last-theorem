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

namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_add

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F) {D E : Divisor K F} (hD : ∀ v ∈ D.support, Place.evalAt v f ≠ 0) (hE : ∀ v ∈ E.support, Place.evalAt v f ≠ 0) : Divisor.evalFun f (D + E) = Divisor.evalFun f D * Divisor.evalFun f E := by
  classical
  refine Finsupp.prod_add_index (fun v _ => zpow_zero _) (fun v hv b₁ b₂ => ?_)
  refine zpow_add₀ ?_ b₁ b₂
  rcases Finset.mem_union.mp hv with h | h
  · exact hD v h
  · exact hE v h
end S_AlgebraicCurve_Divisor_evalFun_add
end P2MW

public section
open AlgebraicCurve
theorem AlgebraicCurve.Divisor.evalFun_add {K F : Type*} [Field K] [Field F] [Algebra K F] (f : F) {D E : Divisor K F} (hD : ∀ v ∈ D.support, Place.evalAt v f ≠ 0) (hE : ∀ v ∈ E.support, Place.evalAt v f ≠ 0) : Divisor.evalFun f (D + E) = Divisor.evalFun f D * Divisor.evalFun f E := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_evalFun_add.solution
end
