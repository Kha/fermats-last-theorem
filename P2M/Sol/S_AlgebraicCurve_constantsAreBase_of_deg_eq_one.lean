module

public import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Sol.S_AlgebraicCurve_constantsAreBase_of_exists_isRational
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
import P2M.Sol.S_AlgebraicCurve_Place_isRational_iff_deg_eq_one

namespace P2MW.S_AlgebraicCurve_constantsAreBase_of_deg_eq_one

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasPrincipalDivisors K F]
    (v₀ : AlgebraicCurve.Place K F) (hdeg : v₀.deg = 1) :
    AlgebraicCurve.ConstantsAreBase K F :=
  AlgebraicCurve.constantsAreBase_of_exists_isRational v₀ ((v₀.isRational_iff_deg_eq_one).mpr hdeg)
    (hdeg ▸ one_ne_zero)
end S_AlgebraicCurve_constantsAreBase_of_deg_eq_one
end P2MW

public section
theorem AlgebraicCurve.constantsAreBase_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasPrincipalDivisors K F]
    (v₀ : AlgebraicCurve.Place K F) (hdeg : v₀.deg = 1) :
    AlgebraicCurve.ConstantsAreBase K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_constantsAreBase_of_deg_eq_one.solution
end
