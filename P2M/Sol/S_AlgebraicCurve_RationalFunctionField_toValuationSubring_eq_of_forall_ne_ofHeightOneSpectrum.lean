module

public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Sol.S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete
import P2M.Sol.S_AlgebraicCurve_Place_adicValuation_isTrivialOn
import P2M.Util
public import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
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

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem solution {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w) : v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := by
  haveI := v.adicValuation_isRankOneDiscrete
  haveI := v.adicValuation_isTrivialOn
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)
  · obtain ⟨w, hw, -⟩ := h
    exact absurd (Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))) (hv w)
end S_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
end P2MW

public section
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve
theorem AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w) : v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum.solution
end
