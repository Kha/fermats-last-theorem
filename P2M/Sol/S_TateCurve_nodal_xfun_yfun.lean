module

public import Definitions.Def_TateCurve_PointSeries
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

namespace P2MW.S_TateCurve_nodal_xfun_yfun
open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    {w : K} (hw1 : w ≠ 1) :
    yfun w ^ 2 + xfun w * yfun w = xfun w ^ 3 := by
  have h1 : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have e2 : xfun w * ((1 : K) - w) ^ 2 = w := by
    rw [xfun, div_mul_cancel₀ _ (pow_ne_zero 2 h1)]
  have e3 : yfun w * ((1 : K) - w) ^ 3 = w ^ 2 := by
    rw [yfun, div_mul_cancel₀ _ (pow_ne_zero 3 h1)]
  apply mul_right_cancel₀ (pow_ne_zero 6 h1)
  calc (yfun w ^ 2 + xfun w * yfun w) * ((1 : K) - w) ^ 6
      = (yfun w * ((1 : K) - w) ^ 3) ^ 2
        + (xfun w * ((1 : K) - w) ^ 2) * (yfun w * ((1 : K) - w) ^ 3) * ((1 : K) - w) := by ring
    _ = (w ^ 2) ^ 2 + w * w ^ 2 * ((1 : K) - w) := by rw [e2, e3]
    _ = w ^ 3 := by ring
    _ = (xfun w * ((1 : K) - w) ^ 2) ^ 3 := by rw [e2]
    _ = xfun w ^ 3 * ((1 : K) - w) ^ 6 := by ring
end S_TateCurve_nodal_xfun_yfun
end P2MW

public section
open TateCurve
open scoped NNReal
theorem TateCurve.nodal_xfun_yfun {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {w : K} (hw1 : w ≠ 1) : yfun w ^ 2 + xfun w * yfun w = xfun w ^ 3 := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_nodal_xfun_yfun.solution
end
