import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve
theorem AlgebraicCurve.RationalFunctionField.isPrincipal_of_degree_eq_zero {K : Type*} [Field K] (D : Divisor K (RatFunc K)) (hD : Divisor.degree D = 0) : D.IsPrincipal := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero.solution
