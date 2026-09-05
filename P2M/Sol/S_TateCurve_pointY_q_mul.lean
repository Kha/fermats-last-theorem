module

public import Definitions.Def_TateCurve_PointSeries
import P2M.Util
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
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

namespace P2MW.S_TateCurve_pointY_q_mul
open TateCurve
open scoped NNReal

private theorem tsum_comp_add_one' {α : Type*} [AddCommGroup α] [UniformSpace α]
    [IsUniformAddGroup α] [CompleteSpace α] [T2Space α] (f : ℤ → α) :
    ∑' n : ℤ, f (n + 1) = ∑' n : ℤ, f n :=
  (Equiv.addRight (1 : ℤ)).tsum_eq f

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) : pointY q (q * u) = pointY q u := by
  have hterm : ∀ n : ℤ, yTerm q (q * u) n = yTerm q u (n + 1) := fun n => by
    rw [yTerm, yTerm, show q ^ n * (q * u) = q ^ (n + 1) * u by rw [zpow_add_one₀ hq0]; ring]
  rw [pointY, pointY]
  congr 1
  calc ∑' n : ℤ, yTerm q (q * u) n = ∑' n : ℤ, yTerm q u (n + 1) := tsum_congr hterm
    _ = ∑' n : ℤ, yTerm q u n := tsum_comp_add_one' _
end S_TateCurve_pointY_q_mul
end P2MW

public section
open TateCurve
open scoped NNReal
theorem TateCurve.pointY_q_mul {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) : pointY q (q * u) = pointY q u := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_pointY_q_mul.solution
end
