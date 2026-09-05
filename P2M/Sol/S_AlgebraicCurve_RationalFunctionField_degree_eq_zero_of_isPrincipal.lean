import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord
import P2M.Util
namespace P2MW.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_isPrincipal
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem solution {K : Type*} [Field K] {D : Divisor K (RatFunc K)} (hD : D.IsPrincipal) : Divisor.degree D = 0 := by
  obtain ⟨f, -, hDf⟩ := hD
  exact AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord D hDf
