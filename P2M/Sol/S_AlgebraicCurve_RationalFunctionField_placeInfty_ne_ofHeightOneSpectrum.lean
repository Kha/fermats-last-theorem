module

public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
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
import Mathlib.NumberTheory.RatFunc.Ostrowski
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
import Definitions.Def_AlgebraicCurve_RatFuncPlaceClassification -- shake: keep

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum

open IsDedekindDomain AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem solution (K : Type*) [Field K] [DecidableEq (RatFunc K)] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) : placeInfty K ≠ Place.ofHeightOneSpectrum w := by
  intro h
  refine RatFunc.adicValuation_not_isEquiv_infty_valuation w
    ((Valuation.isEquiv_iff_valuationSubring _ _).mpr ?_)
  have h2 := congrArg Place.toValuationSubring h
  rw [placeInfty_toValuationSubring, Place.ofHeightOneSpectrum_toValuationSubring] at h2
  exact h2.symm
end S_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum
end P2MW

public section
open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem P2M.Dup.AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum (K : Type*) [Field K] [DecidableEq (RatFunc K)] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) : placeInfty K ≠ Place.ofHeightOneSpectrum w := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum
end
